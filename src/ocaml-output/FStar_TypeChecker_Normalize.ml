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
      fun uu___103_269  ->
        match uu___103_269 with
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
      let add_opt x uu___104_1503 =
        match uu___104_1503 with
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
  fun uu___105_3222  ->
    match uu___105_3222 with
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
  fun uu___106_3284  ->
    match uu___106_3284 with
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
  fun uu___107_3404  ->
    match uu___107_3404 with | [] -> true | uu____3407 -> false
  
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
            (fun uu____3882  ->
               let uu____3883 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3884 = env_to_string env  in
               let uu____3885 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3883 uu____3884 uu____3885);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3894 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3897 ->
                    let uu____3922 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3922
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3923 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3924 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3925 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3926 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar uu____3927 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3949 ->
                           let uu____3966 =
                             let uu____3967 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____3968 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____3967 uu____3968
                              in
                           failwith uu____3966
                       | uu____3971 -> inline_closure_env cfg env stack t1)
                    else rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____3977 =
                        let uu____3978 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____3978  in
                      mk uu____3977 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____3986 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3986  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____3988 = lookup_bvar env x  in
                    (match uu____3988 with
                     | Univ uu____3991 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___151_3995 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___151_3995.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___151_3995.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____4001,uu____4002) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4087  ->
                              fun stack1  ->
                                match uu____4087 with
                                | (a,aq) ->
                                    let uu____4099 =
                                      let uu____4100 =
                                        let uu____4107 =
                                          let uu____4108 =
                                            let uu____4139 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4139, false)  in
                                          Clos uu____4108  in
                                        (uu____4107, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4100  in
                                    uu____4099 :: stack1) args)
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
                    let uu____4333 = close_binders cfg env bs  in
                    (match uu____4333 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4380 =
                      let uu____4391 =
                        let uu____4398 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4398]  in
                      close_binders cfg env uu____4391  in
                    (match uu____4380 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4421 =
                             let uu____4422 =
                               let uu____4429 =
                                 let uu____4430 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4430
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4429, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4422  in
                           mk uu____4421 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4521 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4521
                      | FStar_Util.Inr c ->
                          let uu____4535 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4535
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4554 =
                        let uu____4555 =
                          let uu____4582 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4582, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4555  in
                      mk uu____4554 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4628 =
                            let uu____4629 =
                              let uu____4636 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4636, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4629  in
                          mk uu____4628 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4688  -> dummy :: env1) env
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
                    let uu____4709 =
                      let uu____4720 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4720
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4739 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___152_4755 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___152_4755.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___152_4755.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4739))
                       in
                    (match uu____4709 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___153_4773 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___153_4773.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___153_4773.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___153_4773.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___153_4773.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4787,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4850  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4875 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4875
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4895  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4919 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4919
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___154_4927 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___154_4927.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___154_4927.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___155_4928 = lb  in
                      let uu____4929 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___155_4928.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___155_4928.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4929;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___155_4928.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___155_4928.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____4961  -> fun env1  -> dummy :: env1)
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
            (fun uu____5064  ->
               let uu____5065 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5066 = env_to_string env  in
               let uu____5067 = stack_to_string stack  in
               let uu____5068 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5065 uu____5066 uu____5067 uu____5068);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5073,uu____5074),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5149 = close_binders cfg env' bs  in
               (match uu____5149 with
                | (bs1,uu____5163) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5179 =
                      let uu___156_5180 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___156_5180.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___156_5180.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5179)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5226 =
                 match uu____5226 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5301 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5322 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5382  ->
                                     fun uu____5383  ->
                                       match (uu____5382, uu____5383) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5474 = norm_pat env4 p1
                                              in
                                           (match uu____5474 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5322 with
                            | (pats1,env4) ->
                                ((let uu___157_5556 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___157_5556.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___158_5575 = x  in
                             let uu____5576 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_5575.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_5575.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5576
                             }  in
                           ((let uu___159_5590 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___159_5590.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___160_5601 = x  in
                             let uu____5602 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___160_5601.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___160_5601.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5602
                             }  in
                           ((let uu___161_5616 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___161_5616.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___162_5632 = x  in
                             let uu____5633 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___162_5632.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___162_5632.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5633
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___163_5642 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___163_5642.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5647 = norm_pat env2 pat  in
                     (match uu____5647 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____5692 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____5692
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____5711 =
                   let uu____5712 =
                     let uu____5735 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____5735)  in
                   FStar_Syntax_Syntax.Tm_match uu____5712  in
                 mk uu____5711 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____5830 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____5919  ->
                                       match uu____5919 with
                                       | (a,q) ->
                                           let uu____5938 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____5938, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____5830
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____5949 =
                       let uu____5956 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____5956)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____5949
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____5968 =
                       let uu____5977 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____5977)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____5968
                 | uu____5982 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____5986 -> failwith "Impossible: unexpected stack element")

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
        let uu____6000 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6049  ->
                  fun uu____6050  ->
                    match (uu____6049, uu____6050) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___164_6120 = b  in
                          let uu____6121 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___164_6120.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___164_6120.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6121
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6000 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6214 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6227 = inline_closure_env cfg env [] t  in
                 let uu____6228 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6227 uu____6228
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6241 = inline_closure_env cfg env [] t  in
                 let uu____6242 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6241 uu____6242
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6288  ->
                           match uu____6288 with
                           | (a,q) ->
                               let uu____6301 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6301, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___108_6316  ->
                           match uu___108_6316 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6320 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6320
                           | f -> f))
                    in
                 let uu____6324 =
                   let uu___165_6325 = c1  in
                   let uu____6326 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6326;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___165_6325.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6324)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___109_6336  ->
            match uu___109_6336 with
            | FStar_Syntax_Syntax.DECREASES uu____6337 -> false
            | uu____6340 -> true))

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
                   (fun uu___110_6358  ->
                      match uu___110_6358 with
                      | FStar_Syntax_Syntax.DECREASES uu____6359 -> false
                      | uu____6362 -> true))
               in
            let rc1 =
              let uu___166_6364 = rc  in
              let uu____6365 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___166_6364.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6365;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6374 -> lopt

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
    let uu____6487 =
      let uu____6496 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6496  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6487  in
  let arg_as_bounded_int uu____6522 =
    match uu____6522 with
    | (a,uu____6534) ->
        let uu____6541 =
          let uu____6542 = FStar_Syntax_Subst.compress a  in
          uu____6542.FStar_Syntax_Syntax.n  in
        (match uu____6541 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6552;
                FStar_Syntax_Syntax.vars = uu____6553;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6555;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6556;_},uu____6557)::[])
             when
             let uu____6596 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6596 "int_to_t" ->
             let uu____6597 =
               let uu____6602 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6602)  in
             FStar_Pervasives_Native.Some uu____6597
         | uu____6607 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6655 = f a  in FStar_Pervasives_Native.Some uu____6655
    | uu____6656 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____6712 = f a0 a1  in FStar_Pervasives_Native.Some uu____6712
    | uu____6713 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____6771 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____6771  in
  let binary_op as_a f res args =
    let uu____6836 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____6836  in
  let as_primitive_step is_strong uu____6867 =
    match uu____6867 with
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
           let uu____6927 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____6927)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____6963 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____6963)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____6992 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____6992)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7028 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7028)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7064 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7064)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7196 =
          let uu____7205 = as_a a  in
          let uu____7208 = as_b b  in (uu____7205, uu____7208)  in
        (match uu____7196 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7223 =
               let uu____7224 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7224  in
             FStar_Pervasives_Native.Some uu____7223
         | uu____7225 -> FStar_Pervasives_Native.None)
    | uu____7234 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7254 =
        let uu____7255 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7255  in
      mk uu____7254 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7267 =
      let uu____7270 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7270  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7267  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7312 =
      let uu____7313 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7313  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7312
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7335 = arg_as_string a1  in
        (match uu____7335 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7341 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7341 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7354 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7354
              | uu____7355 -> FStar_Pervasives_Native.None)
         | uu____7360 -> FStar_Pervasives_Native.None)
    | uu____7363 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7377 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7377
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7414 =
          let uu____7435 = arg_as_string fn  in
          let uu____7438 = arg_as_int from_line  in
          let uu____7441 = arg_as_int from_col  in
          let uu____7444 = arg_as_int to_line  in
          let uu____7447 = arg_as_int to_col  in
          (uu____7435, uu____7438, uu____7441, uu____7444, uu____7447)  in
        (match uu____7414 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7478 =
                 let uu____7479 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7480 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7479 uu____7480  in
               let uu____7481 =
                 let uu____7482 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7483 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7482 uu____7483  in
               FStar_Range.mk_range fn1 uu____7478 uu____7481  in
             let uu____7484 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7484
         | uu____7485 -> FStar_Pervasives_Native.None)
    | uu____7506 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____7539)::(a1,uu____7541)::(a2,uu____7543)::[] ->
        let uu____7580 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7580 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____7593 -> FStar_Pervasives_Native.None)
    | uu____7594 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____7625)::[] ->
        let uu____7634 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____7634 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7640 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7640
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7641 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____7667 =
      let uu____7684 =
        let uu____7701 =
          let uu____7718 =
            let uu____7735 =
              let uu____7752 =
                let uu____7769 =
                  let uu____7786 =
                    let uu____7803 =
                      let uu____7820 =
                        let uu____7837 =
                          let uu____7854 =
                            let uu____7871 =
                              let uu____7888 =
                                let uu____7905 =
                                  let uu____7922 =
                                    let uu____7939 =
                                      let uu____7956 =
                                        let uu____7973 =
                                          let uu____7990 =
                                            let uu____8007 =
                                              let uu____8024 =
                                                let uu____8039 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8039,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8048 =
                                                let uu____8065 =
                                                  let uu____8080 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8080,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8093 =
                                                  let uu____8110 =
                                                    let uu____8127 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8127,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8138 =
                                                    let uu____8157 =
                                                      let uu____8174 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8174,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8157]  in
                                                  uu____8110 :: uu____8138
                                                   in
                                                uu____8065 :: uu____8093  in
                                              uu____8024 :: uu____8048  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8007
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____7990
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____7973
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____7956
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____7939
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8402 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8402 y)))
                                    :: uu____7922
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____7905
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____7888
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____7871
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____7854
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____7837
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____7820
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____8597 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____8597)))
                      :: uu____7803
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____8627 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____8627)))
                    :: uu____7786
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____8657 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____8657)))
                  :: uu____7769
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____8687 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____8687)))
                :: uu____7752
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____7735
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____7718
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____7701
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____7684
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____7667
     in
  let weak_ops =
    let uu____8848 =
      let uu____8869 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____8869, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____8848]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____8967 =
        let uu____8972 =
          let uu____8973 = FStar_Syntax_Syntax.as_arg c  in [uu____8973]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____8972  in
      uu____8967 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9029 =
                let uu____9044 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9044, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9066  ->
                          fun uu____9067  ->
                            match (uu____9066, uu____9067) with
                            | ((int_to_t1,x),(uu____9086,y)) ->
                                let uu____9096 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9096)))
                 in
              let uu____9097 =
                let uu____9114 =
                  let uu____9129 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9129, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9151  ->
                            fun uu____9152  ->
                              match (uu____9151, uu____9152) with
                              | ((int_to_t1,x),(uu____9171,y)) ->
                                  let uu____9181 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9181)))
                   in
                let uu____9182 =
                  let uu____9199 =
                    let uu____9214 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9214, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9236  ->
                              fun uu____9237  ->
                                match (uu____9236, uu____9237) with
                                | ((int_to_t1,x),(uu____9256,y)) ->
                                    let uu____9266 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9266)))
                     in
                  let uu____9267 =
                    let uu____9284 =
                      let uu____9299 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9299, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9317  ->
                                match uu____9317 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9284]  in
                  uu____9199 :: uu____9267  in
                uu____9114 :: uu____9182  in
              uu____9029 :: uu____9097))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9447 =
                let uu____9462 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9462, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9484  ->
                          fun uu____9485  ->
                            match (uu____9484, uu____9485) with
                            | ((int_to_t1,x),(uu____9504,y)) ->
                                let uu____9514 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9514)))
                 in
              let uu____9515 =
                let uu____9532 =
                  let uu____9547 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9547, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9569  ->
                            fun uu____9570  ->
                              match (uu____9569, uu____9570) with
                              | ((int_to_t1,x),(uu____9589,y)) ->
                                  let uu____9599 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9599)))
                   in
                [uu____9532]  in
              uu____9447 :: uu____9515))
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
    | (_typ,uu____9729)::(a1,uu____9731)::(a2,uu____9733)::[] ->
        let uu____9770 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9770 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___167_9776 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___167_9776.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___167_9776.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___168_9780 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___168_9780.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___168_9780.FStar_Syntax_Syntax.vars)
                })
         | uu____9781 -> FStar_Pervasives_Native.None)
    | (_typ,uu____9783)::uu____9784::(a1,uu____9786)::(a2,uu____9788)::[] ->
        let uu____9837 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9837 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___167_9843 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___167_9843.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___167_9843.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___168_9847 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___168_9847.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___168_9847.FStar_Syntax_Syntax.vars)
                })
         | uu____9848 -> FStar_Pervasives_Native.None)
    | uu____9849 -> failwith "Unexpected number of arguments"  in
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
    let uu____9903 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____9903 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____9955 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9955) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10017  ->
           fun subst1  ->
             match uu____10017 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10058,uu____10059)) ->
                      let uu____10118 = b  in
                      (match uu____10118 with
                       | (bv,uu____10126) ->
                           let uu____10127 =
                             let uu____10128 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10128  in
                           if uu____10127
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10133 = unembed_binder term1  in
                              match uu____10133 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10140 =
                                      let uu___169_10141 = bv  in
                                      let uu____10142 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___169_10141.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___169_10141.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10142
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10140
                                     in
                                  let b_for_x =
                                    let uu____10146 =
                                      let uu____10153 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10153)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10146  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___111_10163  ->
                                         match uu___111_10163 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10164,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10166;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10167;_})
                                             ->
                                             let uu____10172 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10172
                                         | uu____10173 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10174 -> subst1)) env []
  
let reduce_primops :
  'Auu____10197 'Auu____10198 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10197) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10198 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____10244 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10244 with
             | (head1,args) ->
                 let uu____10281 =
                   let uu____10282 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10282.FStar_Syntax_Syntax.n  in
                 (match uu____10281 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10286 = find_prim_step cfg fv  in
                      (match uu____10286 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10308  ->
                                   let uu____10309 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10310 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10317 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10309 uu____10310 uu____10317);
                              tm)
                           else
                             (let uu____10319 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10319 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10430  ->
                                        let uu____10431 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10431);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10434  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10436 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10436 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10442  ->
                                              let uu____10443 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10443);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10449  ->
                                              let uu____10450 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10451 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10450 uu____10451);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10452 ->
                           (log_primops cfg
                              (fun uu____10456  ->
                                 let uu____10457 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10457);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10461  ->
                            let uu____10462 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10462);
                       (match args with
                        | (a1,uu____10464)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10481 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10493  ->
                            let uu____10494 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10494);
                       (match args with
                        | (t,uu____10496)::(r,uu____10498)::[] ->
                            let uu____10525 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____10525 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___170_10529 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___170_10529.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___170_10529.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____10532 -> tm))
                  | uu____10541 -> tm))
  
let reduce_equality :
  'Auu____10552 'Auu____10553 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10552) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10553 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___171_10597 = cfg  in
         {
           steps =
             (let uu___172_10600 = default_steps  in
              {
                beta = (uu___172_10600.beta);
                iota = (uu___172_10600.iota);
                zeta = (uu___172_10600.zeta);
                weak = (uu___172_10600.weak);
                hnf = (uu___172_10600.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___172_10600.do_not_unfold_pure_lets);
                unfold_until = (uu___172_10600.unfold_until);
                unfold_only = (uu___172_10600.unfold_only);
                unfold_fully = (uu___172_10600.unfold_fully);
                unfold_attr = (uu___172_10600.unfold_attr);
                unfold_tac = (uu___172_10600.unfold_tac);
                pure_subterms_within_computations =
                  (uu___172_10600.pure_subterms_within_computations);
                simplify = (uu___172_10600.simplify);
                erase_universes = (uu___172_10600.erase_universes);
                allow_unbound_universes =
                  (uu___172_10600.allow_unbound_universes);
                reify_ = (uu___172_10600.reify_);
                compress_uvars = (uu___172_10600.compress_uvars);
                no_full_norm = (uu___172_10600.no_full_norm);
                check_no_uvars = (uu___172_10600.check_no_uvars);
                unmeta = (uu___172_10600.unmeta);
                unascribe = (uu___172_10600.unascribe);
                in_full_norm_request = (uu___172_10600.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___172_10600.weakly_reduce_scrutinee)
              });
           tcenv = (uu___171_10597.tcenv);
           debug = (uu___171_10597.debug);
           delta_level = (uu___171_10597.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___171_10597.strong);
           memoize_lazy = (uu___171_10597.memoize_lazy);
           normalize_pure_lets = (uu___171_10597.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____10607 .
    FStar_Syntax_Syntax.term -> 'Auu____10607 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10622 =
        let uu____10629 =
          let uu____10630 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10630.FStar_Syntax_Syntax.n  in
        (uu____10629, args)  in
      match uu____10622 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10636::uu____10637::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10641::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10646::uu____10647::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10650 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___112_10663  ->
    match uu___112_10663 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10669 =
          let uu____10672 =
            let uu____10673 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____10673  in
          [uu____10672]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____10669
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____10679 =
          let uu____10682 =
            let uu____10683 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____10683  in
          [uu____10682]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____10679
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____10704 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10704) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10750 =
          let uu____10755 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____10755 s  in
        match uu____10750 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____10771 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____10771
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____10788::(tm,uu____10790)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____10819)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____10840)::uu____10841::(tm,uu____10843)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____10884 =
            let uu____10889 = full_norm steps  in parse_steps uu____10889  in
          (match uu____10884 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____10928 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___113_10947  ->
    match uu___113_10947 with
    | (App
        (uu____10950,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10951;
                       FStar_Syntax_Syntax.vars = uu____10952;_},uu____10953,uu____10954))::uu____10955
        -> true
    | uu____10962 -> false
  
let firstn :
  'Auu____10971 .
    Prims.int ->
      'Auu____10971 Prims.list ->
        ('Auu____10971 Prims.list,'Auu____10971 Prims.list)
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
          (uu____11013,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11014;
                         FStar_Syntax_Syntax.vars = uu____11015;_},uu____11016,uu____11017))::uu____11018
          -> (cfg.steps).reify_
      | uu____11025 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11048) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11058) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11077  ->
                  match uu____11077 with
                  | (a,uu____11085) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11091 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11116 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11117 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11134 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11135 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11136 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11137 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11138 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11139 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11146 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11153 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11166 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11183 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11196 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11203 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11265  ->
                   match uu____11265 with
                   | (a,uu____11273) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11280) ->
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
                     (fun uu____11402  ->
                        match uu____11402 with
                        | (a,uu____11410) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11415,uu____11416,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11422,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11428 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11435 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11436 -> false))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____11728 ->
                   let uu____11753 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____11753
               | uu____11754 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____11762  ->
               let uu____11763 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____11764 = FStar_Syntax_Print.term_to_string t1  in
               let uu____11765 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____11772 =
                 let uu____11773 =
                   let uu____11776 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11776
                    in
                 stack_to_string uu____11773  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11763 uu____11764 uu____11765 uu____11772);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11799 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11800 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____11801 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11802;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_18;
                 FStar_Syntax_Syntax.fv_qual = uu____11803;_}
               when _0_18 = (Prims.parse_int "0") -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11806;
                 FStar_Syntax_Syntax.fv_delta = uu____11807;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11808;
                 FStar_Syntax_Syntax.fv_delta = uu____11809;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11810);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____11817 ->
               let uu____11824 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____11824
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____11854 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____11854)
               ->
               let cfg' =
                 let uu___173_11856 = cfg  in
                 {
                   steps =
                     (let uu___174_11859 = cfg.steps  in
                      {
                        beta = (uu___174_11859.beta);
                        iota = (uu___174_11859.iota);
                        zeta = (uu___174_11859.zeta);
                        weak = (uu___174_11859.weak);
                        hnf = (uu___174_11859.hnf);
                        primops = (uu___174_11859.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___174_11859.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___174_11859.unfold_attr);
                        unfold_tac = (uu___174_11859.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___174_11859.pure_subterms_within_computations);
                        simplify = (uu___174_11859.simplify);
                        erase_universes = (uu___174_11859.erase_universes);
                        allow_unbound_universes =
                          (uu___174_11859.allow_unbound_universes);
                        reify_ = (uu___174_11859.reify_);
                        compress_uvars = (uu___174_11859.compress_uvars);
                        no_full_norm = (uu___174_11859.no_full_norm);
                        check_no_uvars = (uu___174_11859.check_no_uvars);
                        unmeta = (uu___174_11859.unmeta);
                        unascribe = (uu___174_11859.unascribe);
                        in_full_norm_request =
                          (uu___174_11859.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___174_11859.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___173_11856.tcenv);
                   debug = (uu___173_11856.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___173_11856.primitive_steps);
                   strong = (uu___173_11856.strong);
                   memoize_lazy = (uu___173_11856.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____11864 = get_norm_request (norm cfg' env []) args  in
               (match uu____11864 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____11895  ->
                              fun stack1  ->
                                match uu____11895 with
                                | (a,aq) ->
                                    let uu____11907 =
                                      let uu____11908 =
                                        let uu____11915 =
                                          let uu____11916 =
                                            let uu____11947 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____11947, false)  in
                                          Clos uu____11916  in
                                        (uu____11915, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11908  in
                                    uu____11907 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____12031  ->
                          let uu____12032 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12032);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____12054 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___114_12059  ->
                                match uu___114_12059 with
                                | UnfoldUntil uu____12060 -> true
                                | UnfoldOnly uu____12061 -> true
                                | UnfoldFully uu____12064 -> true
                                | uu____12067 -> false))
                         in
                      if uu____12054
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___175_12072 = cfg  in
                      let uu____12073 =
                        let uu___176_12074 = to_fsteps s  in
                        {
                          beta = (uu___176_12074.beta);
                          iota = (uu___176_12074.iota);
                          zeta = (uu___176_12074.zeta);
                          weak = (uu___176_12074.weak);
                          hnf = (uu___176_12074.hnf);
                          primops = (uu___176_12074.primops);
                          do_not_unfold_pure_lets =
                            (uu___176_12074.do_not_unfold_pure_lets);
                          unfold_until = (uu___176_12074.unfold_until);
                          unfold_only = (uu___176_12074.unfold_only);
                          unfold_fully = (uu___176_12074.unfold_fully);
                          unfold_attr = (uu___176_12074.unfold_attr);
                          unfold_tac = (uu___176_12074.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___176_12074.pure_subterms_within_computations);
                          simplify = (uu___176_12074.simplify);
                          erase_universes = (uu___176_12074.erase_universes);
                          allow_unbound_universes =
                            (uu___176_12074.allow_unbound_universes);
                          reify_ = (uu___176_12074.reify_);
                          compress_uvars = (uu___176_12074.compress_uvars);
                          no_full_norm = (uu___176_12074.no_full_norm);
                          check_no_uvars = (uu___176_12074.check_no_uvars);
                          unmeta = (uu___176_12074.unmeta);
                          unascribe = (uu___176_12074.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___176_12074.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____12073;
                        tcenv = (uu___175_12072.tcenv);
                        debug = (uu___175_12072.debug);
                        delta_level;
                        primitive_steps = (uu___175_12072.primitive_steps);
                        strong = (uu___175_12072.strong);
                        memoize_lazy = (uu___175_12072.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12083 =
                          let uu____12084 =
                            let uu____12089 = FStar_Util.now ()  in
                            (t1, uu____12089)  in
                          Debug uu____12084  in
                        uu____12083 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12093 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12093
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12102 =
                      let uu____12109 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12109, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12102  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12119 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12119  in
               let uu____12120 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____12120
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____12126  ->
                       let uu____12127 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12128 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12127 uu____12128);
                  if b
                  then
                    (let uu____12129 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____12129 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____12137 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____12137) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____12150),uu____12151);
                                FStar_Syntax_Syntax.sigrng = uu____12152;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____12154;
                                FStar_Syntax_Syntax.sigattrs = uu____12155;_},uu____12156),uu____12157)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____12222 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___115_12226  ->
                               match uu___115_12226 with
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
                          (let uu____12236 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____12236))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____12255) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____12290,uu____12291) -> false)))
                     in
                  let uu____12308 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____12324 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____12324 then (true, true) else (false, false)
                     in
                  match uu____12308 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____12337  ->
                            let uu____12338 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____12339 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____12340 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____12338 uu____12339 uu____12340);
                       if should_delta2
                       then
                         (let uu____12341 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___177_12357 = cfg  in
                                 {
                                   steps =
                                     (let uu___178_12360 = cfg.steps  in
                                      {
                                        beta = (uu___178_12360.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___178_12360.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___178_12360.unfold_attr);
                                        unfold_tac =
                                          (uu___178_12360.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___178_12360.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___178_12360.erase_universes);
                                        allow_unbound_universes =
                                          (uu___178_12360.allow_unbound_universes);
                                        reify_ = (uu___178_12360.reify_);
                                        compress_uvars =
                                          (uu___178_12360.compress_uvars);
                                        no_full_norm =
                                          (uu___178_12360.no_full_norm);
                                        check_no_uvars =
                                          (uu___178_12360.check_no_uvars);
                                        unmeta = (uu___178_12360.unmeta);
                                        unascribe =
                                          (uu___178_12360.unascribe);
                                        in_full_norm_request =
                                          (uu___178_12360.in_full_norm_request);
                                        weakly_reduce_scrutinee =
                                          (uu___178_12360.weakly_reduce_scrutinee)
                                      });
                                   tcenv = (uu___177_12357.tcenv);
                                   debug = (uu___177_12357.debug);
                                   delta_level = (uu___177_12357.delta_level);
                                   primitive_steps =
                                     (uu___177_12357.primitive_steps);
                                   strong = (uu___177_12357.strong);
                                   memoize_lazy =
                                     (uu___177_12357.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___177_12357.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____12341 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12374 = lookup_bvar env x  in
               (match uu____12374 with
                | Univ uu____12375 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12424 = FStar_ST.op_Bang r  in
                      (match uu____12424 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12546  ->
                                 let uu____12547 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12548 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12547
                                   uu____12548);
                            (let uu____12549 = maybe_weakly_reduced t'  in
                             if uu____12549
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____12550 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12621)::uu____12622 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12631)::uu____12632 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12644,uu____12645))::stack_rest ->
                    (match c with
                     | Univ uu____12649 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12658 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12679  ->
                                    let uu____12680 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12680);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12720  ->
                                    let uu____12721 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12721);
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
                       (fun uu____12799  ->
                          let uu____12800 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12800);
                     norm cfg env stack1 t1)
                | (Debug uu____12801)::uu____12802 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___179_12812 = cfg.steps  in
                             {
                               beta = (uu___179_12812.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___179_12812.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___179_12812.unfold_until);
                               unfold_only = (uu___179_12812.unfold_only);
                               unfold_fully = (uu___179_12812.unfold_fully);
                               unfold_attr = (uu___179_12812.unfold_attr);
                               unfold_tac = (uu___179_12812.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___179_12812.erase_universes);
                               allow_unbound_universes =
                                 (uu___179_12812.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___179_12812.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___179_12812.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___179_12812.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___179_12812.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___180_12814 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___180_12814.tcenv);
                               debug = (uu___180_12814.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___180_12814.primitive_steps);
                               strong = (uu___180_12814.strong);
                               memoize_lazy = (uu___180_12814.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___180_12814.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12816 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12816 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12858  -> dummy :: env1) env)
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
                                          let uu____12895 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12895)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___181_12900 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___181_12900.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___181_12900.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12901 -> lopt  in
                           (log cfg
                              (fun uu____12907  ->
                                 let uu____12908 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12908);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___182_12917 = cfg  in
                               {
                                 steps = (uu___182_12917.steps);
                                 tcenv = (uu___182_12917.tcenv);
                                 debug = (uu___182_12917.debug);
                                 delta_level = (uu___182_12917.delta_level);
                                 primitive_steps =
                                   (uu___182_12917.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___182_12917.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___182_12917.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12928)::uu____12929 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___179_12941 = cfg.steps  in
                             {
                               beta = (uu___179_12941.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___179_12941.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___179_12941.unfold_until);
                               unfold_only = (uu___179_12941.unfold_only);
                               unfold_fully = (uu___179_12941.unfold_fully);
                               unfold_attr = (uu___179_12941.unfold_attr);
                               unfold_tac = (uu___179_12941.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___179_12941.erase_universes);
                               allow_unbound_universes =
                                 (uu___179_12941.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___179_12941.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___179_12941.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___179_12941.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___179_12941.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___180_12943 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___180_12943.tcenv);
                               debug = (uu___180_12943.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___180_12943.primitive_steps);
                               strong = (uu___180_12943.strong);
                               memoize_lazy = (uu___180_12943.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___180_12943.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12945 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12945 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12987  -> dummy :: env1) env)
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
                                          let uu____13024 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13024)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___181_13029 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___181_13029.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___181_13029.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13030 -> lopt  in
                           (log cfg
                              (fun uu____13036  ->
                                 let uu____13037 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13037);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___182_13046 = cfg  in
                               {
                                 steps = (uu___182_13046.steps);
                                 tcenv = (uu___182_13046.tcenv);
                                 debug = (uu___182_13046.debug);
                                 delta_level = (uu___182_13046.delta_level);
                                 primitive_steps =
                                   (uu___182_13046.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___182_13046.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___182_13046.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13057)::uu____13058 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___179_13072 = cfg.steps  in
                             {
                               beta = (uu___179_13072.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___179_13072.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___179_13072.unfold_until);
                               unfold_only = (uu___179_13072.unfold_only);
                               unfold_fully = (uu___179_13072.unfold_fully);
                               unfold_attr = (uu___179_13072.unfold_attr);
                               unfold_tac = (uu___179_13072.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___179_13072.erase_universes);
                               allow_unbound_universes =
                                 (uu___179_13072.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___179_13072.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___179_13072.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___179_13072.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___179_13072.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___180_13074 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___180_13074.tcenv);
                               debug = (uu___180_13074.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___180_13074.primitive_steps);
                               strong = (uu___180_13074.strong);
                               memoize_lazy = (uu___180_13074.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___180_13074.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13076 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13076 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13118  -> dummy :: env1) env)
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
                                          let uu____13155 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13155)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___181_13160 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___181_13160.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___181_13160.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13161 -> lopt  in
                           (log cfg
                              (fun uu____13167  ->
                                 let uu____13168 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13168);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___182_13177 = cfg  in
                               {
                                 steps = (uu___182_13177.steps);
                                 tcenv = (uu___182_13177.tcenv);
                                 debug = (uu___182_13177.debug);
                                 delta_level = (uu___182_13177.delta_level);
                                 primitive_steps =
                                   (uu___182_13177.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___182_13177.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___182_13177.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13188)::uu____13189 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___179_13203 = cfg.steps  in
                             {
                               beta = (uu___179_13203.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___179_13203.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___179_13203.unfold_until);
                               unfold_only = (uu___179_13203.unfold_only);
                               unfold_fully = (uu___179_13203.unfold_fully);
                               unfold_attr = (uu___179_13203.unfold_attr);
                               unfold_tac = (uu___179_13203.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___179_13203.erase_universes);
                               allow_unbound_universes =
                                 (uu___179_13203.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___179_13203.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___179_13203.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___179_13203.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___179_13203.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___180_13205 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___180_13205.tcenv);
                               debug = (uu___180_13205.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___180_13205.primitive_steps);
                               strong = (uu___180_13205.strong);
                               memoize_lazy = (uu___180_13205.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___180_13205.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13207 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13207 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13249  -> dummy :: env1) env)
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
                                          let uu____13286 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13286)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___181_13291 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___181_13291.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___181_13291.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13292 -> lopt  in
                           (log cfg
                              (fun uu____13298  ->
                                 let uu____13299 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13299);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___182_13308 = cfg  in
                               {
                                 steps = (uu___182_13308.steps);
                                 tcenv = (uu___182_13308.tcenv);
                                 debug = (uu___182_13308.debug);
                                 delta_level = (uu___182_13308.delta_level);
                                 primitive_steps =
                                   (uu___182_13308.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___182_13308.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___182_13308.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13319)::uu____13320 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___179_13338 = cfg.steps  in
                             {
                               beta = (uu___179_13338.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___179_13338.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___179_13338.unfold_until);
                               unfold_only = (uu___179_13338.unfold_only);
                               unfold_fully = (uu___179_13338.unfold_fully);
                               unfold_attr = (uu___179_13338.unfold_attr);
                               unfold_tac = (uu___179_13338.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___179_13338.erase_universes);
                               allow_unbound_universes =
                                 (uu___179_13338.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___179_13338.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___179_13338.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___179_13338.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___179_13338.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___180_13340 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___180_13340.tcenv);
                               debug = (uu___180_13340.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___180_13340.primitive_steps);
                               strong = (uu___180_13340.strong);
                               memoize_lazy = (uu___180_13340.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___180_13340.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13342 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13342 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13384  -> dummy :: env1) env)
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
                                          let uu____13421 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13421)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___181_13426 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___181_13426.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___181_13426.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13427 -> lopt  in
                           (log cfg
                              (fun uu____13433  ->
                                 let uu____13434 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13434);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___182_13443 = cfg  in
                               {
                                 steps = (uu___182_13443.steps);
                                 tcenv = (uu___182_13443.tcenv);
                                 debug = (uu___182_13443.debug);
                                 delta_level = (uu___182_13443.delta_level);
                                 primitive_steps =
                                   (uu___182_13443.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___182_13443.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___182_13443.normalize_pure_lets)
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
                             let uu___179_13457 = cfg.steps  in
                             {
                               beta = (uu___179_13457.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___179_13457.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___179_13457.unfold_until);
                               unfold_only = (uu___179_13457.unfold_only);
                               unfold_fully = (uu___179_13457.unfold_fully);
                               unfold_attr = (uu___179_13457.unfold_attr);
                               unfold_tac = (uu___179_13457.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___179_13457.erase_universes);
                               allow_unbound_universes =
                                 (uu___179_13457.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___179_13457.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___179_13457.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___179_13457.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___179_13457.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___180_13459 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___180_13459.tcenv);
                               debug = (uu___180_13459.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___180_13459.primitive_steps);
                               strong = (uu___180_13459.strong);
                               memoize_lazy = (uu___180_13459.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___180_13459.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13461 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13461 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13503  -> dummy :: env1) env)
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
                                          let uu____13540 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13540)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___181_13545 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___181_13545.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___181_13545.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13546 -> lopt  in
                           (log cfg
                              (fun uu____13552  ->
                                 let uu____13553 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13553);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___182_13562 = cfg  in
                               {
                                 steps = (uu___182_13562.steps);
                                 tcenv = (uu___182_13562.tcenv);
                                 debug = (uu___182_13562.debug);
                                 delta_level = (uu___182_13562.delta_level);
                                 primitive_steps =
                                   (uu___182_13562.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___182_13562.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___182_13562.normalize_pure_lets)
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
                      (fun uu____13611  ->
                         fun stack1  ->
                           match uu____13611 with
                           | (a,aq) ->
                               let uu____13623 =
                                 let uu____13624 =
                                   let uu____13631 =
                                     let uu____13632 =
                                       let uu____13663 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____13663, false)  in
                                     Clos uu____13632  in
                                   (uu____13631, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____13624  in
                               uu____13623 :: stack1) args)
                  in
               (log cfg
                  (fun uu____13747  ->
                     let uu____13748 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13748);
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
                             ((let uu___183_13784 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___183_13784.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___183_13784.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____13785 ->
                      let uu____13790 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13790)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____13793 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____13793 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____13824 =
                          let uu____13825 =
                            let uu____13832 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___184_13834 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___184_13834.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___184_13834.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13832)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____13825  in
                        mk uu____13824 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____13853 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____13853
               else
                 (let uu____13855 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____13855 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13863 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13887  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____13863 c1  in
                      let t2 =
                        let uu____13909 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____13909 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14020)::uu____14021 ->
                    (log cfg
                       (fun uu____14034  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14035)::uu____14036 ->
                    (log cfg
                       (fun uu____14047  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14048,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14049;
                                   FStar_Syntax_Syntax.vars = uu____14050;_},uu____14051,uu____14052))::uu____14053
                    ->
                    (log cfg
                       (fun uu____14062  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14063)::uu____14064 ->
                    (log cfg
                       (fun uu____14075  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14076 ->
                    (log cfg
                       (fun uu____14079  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14083  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14100 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14100
                         | FStar_Util.Inr c ->
                             let uu____14108 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14108
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14121 =
                               let uu____14122 =
                                 let uu____14149 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14149, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14122
                                in
                             mk uu____14121 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14168 ->
                           let uu____14169 =
                             let uu____14170 =
                               let uu____14171 =
                                 let uu____14198 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14198, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14171
                                in
                             mk uu____14170 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14169))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 if
                   ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee)
                     && (Prims.op_Negation (cfg.steps).weak)
                 then
                   let uu___185_14275 = cfg  in
                   {
                     steps =
                       (let uu___186_14278 = cfg.steps  in
                        {
                          beta = (uu___186_14278.beta);
                          iota = (uu___186_14278.iota);
                          zeta = (uu___186_14278.zeta);
                          weak = true;
                          hnf = (uu___186_14278.hnf);
                          primops = (uu___186_14278.primops);
                          do_not_unfold_pure_lets =
                            (uu___186_14278.do_not_unfold_pure_lets);
                          unfold_until = (uu___186_14278.unfold_until);
                          unfold_only = (uu___186_14278.unfold_only);
                          unfold_fully = (uu___186_14278.unfold_fully);
                          unfold_attr = (uu___186_14278.unfold_attr);
                          unfold_tac = (uu___186_14278.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___186_14278.pure_subterms_within_computations);
                          simplify = (uu___186_14278.simplify);
                          erase_universes = (uu___186_14278.erase_universes);
                          allow_unbound_universes =
                            (uu___186_14278.allow_unbound_universes);
                          reify_ = (uu___186_14278.reify_);
                          compress_uvars = (uu___186_14278.compress_uvars);
                          no_full_norm = (uu___186_14278.no_full_norm);
                          check_no_uvars = (uu___186_14278.check_no_uvars);
                          unmeta = (uu___186_14278.unmeta);
                          unascribe = (uu___186_14278.unascribe);
                          in_full_norm_request =
                            (uu___186_14278.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___186_14278.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___185_14275.tcenv);
                     debug = (uu___185_14275.debug);
                     delta_level = (uu___185_14275.delta_level);
                     primitive_steps = (uu___185_14275.primitive_steps);
                     strong = (uu___185_14275.strong);
                     memoize_lazy = (uu___185_14275.memoize_lazy);
                     normalize_pure_lets =
                       (uu___185_14275.normalize_pure_lets)
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
                         let uu____14314 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14314 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___187_14334 = cfg  in
                               let uu____14335 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___187_14334.steps);
                                 tcenv = uu____14335;
                                 debug = (uu___187_14334.debug);
                                 delta_level = (uu___187_14334.delta_level);
                                 primitive_steps =
                                   (uu___187_14334.primitive_steps);
                                 strong = (uu___187_14334.strong);
                                 memoize_lazy = (uu___187_14334.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___187_14334.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14342 =
                                 let uu____14343 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14343  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14342
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___188_14346 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___188_14346.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___188_14346.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___188_14346.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___188_14346.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____14347 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14347
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14358,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14359;
                               FStar_Syntax_Syntax.lbunivs = uu____14360;
                               FStar_Syntax_Syntax.lbtyp = uu____14361;
                               FStar_Syntax_Syntax.lbeff = uu____14362;
                               FStar_Syntax_Syntax.lbdef = uu____14363;
                               FStar_Syntax_Syntax.lbattrs = uu____14364;
                               FStar_Syntax_Syntax.lbpos = uu____14365;_}::uu____14366),uu____14367)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14407 =
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
               if uu____14407
               then
                 let binder =
                   let uu____14409 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14409  in
                 let env1 =
                   let uu____14419 =
                     let uu____14426 =
                       let uu____14427 =
                         let uu____14458 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14458,
                           false)
                          in
                       Clos uu____14427  in
                     ((FStar_Pervasives_Native.Some binder), uu____14426)  in
                   uu____14419 :: env  in
                 (log cfg
                    (fun uu____14551  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____14555  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14556 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14556))
                 else
                   (let uu____14558 =
                      let uu____14563 =
                        let uu____14564 =
                          let uu____14565 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14565
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14564]  in
                      FStar_Syntax_Subst.open_term uu____14563 body  in
                    match uu____14558 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14574  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14582 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14582  in
                            FStar_Util.Inl
                              (let uu___189_14592 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___189_14592.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___189_14592.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____14595  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___190_14597 = lb  in
                             let uu____14598 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___190_14597.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___190_14597.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14598;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___190_14597.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___190_14597.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14633  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___191_14656 = cfg  in
                             {
                               steps = (uu___191_14656.steps);
                               tcenv = (uu___191_14656.tcenv);
                               debug = (uu___191_14656.debug);
                               delta_level = (uu___191_14656.delta_level);
                               primitive_steps =
                                 (uu___191_14656.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___191_14656.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___191_14656.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____14659  ->
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
               let uu____14676 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____14676 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____14712 =
                               let uu___192_14713 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___192_14713.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___192_14713.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____14712  in
                           let uu____14714 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____14714 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____14740 =
                                   FStar_List.map (fun uu____14756  -> dummy)
                                     lbs1
                                    in
                                 let uu____14757 =
                                   let uu____14766 =
                                     FStar_List.map
                                       (fun uu____14786  -> dummy) xs1
                                      in
                                   FStar_List.append uu____14766 env  in
                                 FStar_List.append uu____14740 uu____14757
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14810 =
                                       let uu___193_14811 = rc  in
                                       let uu____14812 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___193_14811.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14812;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___193_14811.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____14810
                                 | uu____14819 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___194_14823 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___194_14823.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___194_14823.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___194_14823.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___194_14823.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____14833 =
                        FStar_List.map (fun uu____14849  -> dummy) lbs2  in
                      FStar_List.append uu____14833 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____14857 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____14857 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___195_14873 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___195_14873.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___195_14873.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____14900 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____14900
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14919 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14995  ->
                        match uu____14995 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___196_15116 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___196_15116.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___196_15116.FStar_Syntax_Syntax.sort)
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
               (match uu____14919 with
                | (rec_env,memos,uu____15329) ->
                    let uu____15382 =
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
                             let uu____15705 =
                               let uu____15712 =
                                 let uu____15713 =
                                   let uu____15744 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15744, false)
                                    in
                                 Clos uu____15713  in
                               (FStar_Pervasives_Native.None, uu____15712)
                                in
                             uu____15705 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____15854  ->
                     let uu____15855 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15855);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____15877 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____15879::uu____15880 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____15885) ->
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
                             | uu____15908 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____15922 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____15922
                              | uu____15933 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____15937 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____15963 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____15981 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____15998 =
                        let uu____15999 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16000 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____15999 uu____16000
                         in
                      failwith uu____15998
                    else rebuild cfg env stack t2
                | uu____16002 -> norm cfg env stack t2))

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
                let uu____16012 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16012  in
              let uu____16013 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16013 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16026  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16037  ->
                        let uu____16038 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16039 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16038 uu____16039);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____16044 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____16044 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____16053))::stack1 ->
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
                      | uu____16108 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____16111 ->
                          let uu____16114 =
                            let uu____16115 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16115
                             in
                          failwith uu____16114
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
                  let uu___197_16139 = cfg  in
                  let uu____16140 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____16140;
                    tcenv = (uu___197_16139.tcenv);
                    debug = (uu___197_16139.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___197_16139.primitive_steps);
                    strong = (uu___197_16139.strong);
                    memoize_lazy = (uu___197_16139.memoize_lazy);
                    normalize_pure_lets =
                      (uu___197_16139.normalize_pure_lets)
                  }
                else
                  (let uu___198_16142 = cfg  in
                   {
                     steps =
                       (let uu___199_16145 = cfg.steps  in
                        {
                          beta = (uu___199_16145.beta);
                          iota = (uu___199_16145.iota);
                          zeta = false;
                          weak = (uu___199_16145.weak);
                          hnf = (uu___199_16145.hnf);
                          primops = (uu___199_16145.primops);
                          do_not_unfold_pure_lets =
                            (uu___199_16145.do_not_unfold_pure_lets);
                          unfold_until = (uu___199_16145.unfold_until);
                          unfold_only = (uu___199_16145.unfold_only);
                          unfold_fully = (uu___199_16145.unfold_fully);
                          unfold_attr = (uu___199_16145.unfold_attr);
                          unfold_tac = (uu___199_16145.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___199_16145.pure_subterms_within_computations);
                          simplify = (uu___199_16145.simplify);
                          erase_universes = (uu___199_16145.erase_universes);
                          allow_unbound_universes =
                            (uu___199_16145.allow_unbound_universes);
                          reify_ = (uu___199_16145.reify_);
                          compress_uvars = (uu___199_16145.compress_uvars);
                          no_full_norm = (uu___199_16145.no_full_norm);
                          check_no_uvars = (uu___199_16145.check_no_uvars);
                          unmeta = (uu___199_16145.unmeta);
                          unascribe = (uu___199_16145.unascribe);
                          in_full_norm_request =
                            (uu___199_16145.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___199_16145.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___198_16142.tcenv);
                     debug = (uu___198_16142.debug);
                     delta_level = (uu___198_16142.delta_level);
                     primitive_steps = (uu___198_16142.primitive_steps);
                     strong = (uu___198_16142.strong);
                     memoize_lazy = (uu___198_16142.memoize_lazy);
                     normalize_pure_lets =
                       (uu___198_16142.normalize_pure_lets)
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
                  (fun uu____16175  ->
                     let uu____16176 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16177 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16176
                       uu____16177);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____16179 =
                   let uu____16180 = FStar_Syntax_Subst.compress head3  in
                   uu____16180.FStar_Syntax_Syntax.n  in
                 match uu____16179 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____16198 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16198
                        in
                     let uu____16199 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16199 with
                      | (uu____16200,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16206 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16216 =
                                   let uu____16217 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16217.FStar_Syntax_Syntax.n  in
                                 match uu____16216 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16223,uu____16224))
                                     ->
                                     let uu____16233 =
                                       let uu____16234 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16234.FStar_Syntax_Syntax.n  in
                                     (match uu____16233 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16240,msrc,uu____16242))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16251 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16251
                                      | uu____16252 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16253 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16254 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16254 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___200_16259 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___200_16259.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___200_16259.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___200_16259.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___200_16259.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___200_16259.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____16260 = FStar_List.tl stack  in
                                    let uu____16261 =
                                      let uu____16262 =
                                        let uu____16269 =
                                          let uu____16270 =
                                            let uu____16283 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16283)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16270
                                           in
                                        FStar_Syntax_Syntax.mk uu____16269
                                         in
                                      uu____16262
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16260 uu____16261
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16299 =
                                      let uu____16300 = is_return body  in
                                      match uu____16300 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16304;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16305;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16310 -> false  in
                                    if uu____16299
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
                                         let uu____16333 =
                                           let uu____16340 =
                                             let uu____16341 =
                                               let uu____16358 =
                                                 let uu____16361 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16361]  in
                                               (uu____16358, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16341
                                              in
                                           FStar_Syntax_Syntax.mk uu____16340
                                            in
                                         uu____16333
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16379 =
                                           let uu____16380 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16380.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16379 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16386::uu____16387::[])
                                             ->
                                             let uu____16394 =
                                               let uu____16401 =
                                                 let uu____16402 =
                                                   let uu____16409 =
                                                     let uu____16412 =
                                                       let uu____16413 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16413
                                                        in
                                                     let uu____16414 =
                                                       let uu____16417 =
                                                         let uu____16418 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16418
                                                          in
                                                       [uu____16417]  in
                                                     uu____16412 ::
                                                       uu____16414
                                                      in
                                                   (bind1, uu____16409)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16402
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16401
                                                in
                                             uu____16394
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16426 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____16432 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____16432
                                         then
                                           let uu____16435 =
                                             let uu____16436 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16436
                                              in
                                           let uu____16437 =
                                             let uu____16440 =
                                               let uu____16441 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____16441
                                                in
                                             [uu____16440]  in
                                           uu____16435 :: uu____16437
                                         else []  in
                                       let reified =
                                         let uu____16446 =
                                           let uu____16453 =
                                             let uu____16454 =
                                               let uu____16469 =
                                                 let uu____16472 =
                                                   let uu____16475 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____16476 =
                                                     let uu____16479 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____16479]  in
                                                   uu____16475 :: uu____16476
                                                    in
                                                 let uu____16480 =
                                                   let uu____16483 =
                                                     let uu____16486 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16487 =
                                                       let uu____16490 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____16491 =
                                                         let uu____16494 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____16495 =
                                                           let uu____16498 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____16498]  in
                                                         uu____16494 ::
                                                           uu____16495
                                                          in
                                                       uu____16490 ::
                                                         uu____16491
                                                        in
                                                     uu____16486 ::
                                                       uu____16487
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____16483
                                                    in
                                                 FStar_List.append
                                                   uu____16472 uu____16480
                                                  in
                                               (bind_inst, uu____16469)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16454
                                              in
                                           FStar_Syntax_Syntax.mk uu____16453
                                            in
                                         uu____16446
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____16510  ->
                                            let uu____16511 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____16512 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____16511 uu____16512);
                                       (let uu____16513 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____16513 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____16537 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16537
                        in
                     let uu____16538 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16538 with
                      | (uu____16539,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____16578 =
                                  let uu____16579 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____16579.FStar_Syntax_Syntax.n  in
                                match uu____16578 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____16585) -> t2
                                | uu____16590 -> head4  in
                              let uu____16591 =
                                let uu____16592 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____16592.FStar_Syntax_Syntax.n  in
                              match uu____16591 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____16598 -> FStar_Pervasives_Native.None
                               in
                            let uu____16599 = maybe_extract_fv head4  in
                            match uu____16599 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____16609 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____16609
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____16614 = maybe_extract_fv head5
                                     in
                                  match uu____16614 with
                                  | FStar_Pervasives_Native.Some uu____16619
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____16620 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____16625 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____16642 =
                              match uu____16642 with
                              | (e,q) ->
                                  let uu____16649 =
                                    let uu____16650 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____16650.FStar_Syntax_Syntax.n  in
                                  (match uu____16649 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____16665 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____16665
                                   | uu____16666 -> false)
                               in
                            let uu____16667 =
                              let uu____16668 =
                                let uu____16675 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____16675 :: args  in
                              FStar_Util.for_some is_arg_impure uu____16668
                               in
                            if uu____16667
                            then
                              let uu____16680 =
                                let uu____16681 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____16681
                                 in
                              failwith uu____16680
                            else ());
                           (let uu____16683 = maybe_unfold_action head_app
                               in
                            match uu____16683 with
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
                                   (fun uu____16726  ->
                                      let uu____16727 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____16728 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____16727 uu____16728);
                                 (let uu____16729 = FStar_List.tl stack  in
                                  norm cfg env uu____16729 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____16731) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____16755 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____16755  in
                     (log cfg
                        (fun uu____16759  ->
                           let uu____16760 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____16760);
                      (let uu____16761 = FStar_List.tl stack  in
                       norm cfg env uu____16761 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____16882  ->
                               match uu____16882 with
                               | (pat,wopt,tm) ->
                                   let uu____16930 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____16930)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____16962 = FStar_List.tl stack  in
                     norm cfg env uu____16962 tm
                 | uu____16963 -> fallback ())

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
              (fun uu____16977  ->
                 let uu____16978 = FStar_Ident.string_of_lid msrc  in
                 let uu____16979 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16980 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16978
                   uu____16979 uu____16980);
            (let uu____16981 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____16981
             then
               let ed =
                 let uu____16983 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____16983  in
               let uu____16984 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____16984 with
               | (uu____16985,return_repr) ->
                   let return_inst =
                     let uu____16994 =
                       let uu____16995 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____16995.FStar_Syntax_Syntax.n  in
                     match uu____16994 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17001::[]) ->
                         let uu____17008 =
                           let uu____17015 =
                             let uu____17016 =
                               let uu____17023 =
                                 let uu____17026 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17026]  in
                               (return_tm, uu____17023)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17016  in
                           FStar_Syntax_Syntax.mk uu____17015  in
                         uu____17008 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17034 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17037 =
                     let uu____17044 =
                       let uu____17045 =
                         let uu____17060 =
                           let uu____17063 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17064 =
                             let uu____17067 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17067]  in
                           uu____17063 :: uu____17064  in
                         (return_inst, uu____17060)  in
                       FStar_Syntax_Syntax.Tm_app uu____17045  in
                     FStar_Syntax_Syntax.mk uu____17044  in
                   uu____17037 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17076 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17076 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17079 =
                      let uu____17080 = FStar_Ident.text_of_lid msrc  in
                      let uu____17081 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17080 uu____17081
                       in
                    failwith uu____17079
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17082;
                      FStar_TypeChecker_Env.mtarget = uu____17083;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17084;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17106 =
                      let uu____17107 = FStar_Ident.text_of_lid msrc  in
                      let uu____17108 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17107 uu____17108
                       in
                    failwith uu____17106
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17109;
                      FStar_TypeChecker_Env.mtarget = uu____17110;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17111;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____17146 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____17147 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____17146 t FStar_Syntax_Syntax.tun uu____17147))

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
                (fun uu____17203  ->
                   match uu____17203 with
                   | (a,imp) ->
                       let uu____17214 = norm cfg env [] a  in
                       (uu____17214, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____17222  ->
             let uu____17223 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17224 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____17223 uu____17224);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17248 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____17248
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___201_17251 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___201_17251.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___201_17251.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17271 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                     uu____17271
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___202_17274 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___202_17274.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___202_17274.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17309  ->
                      match uu____17309 with
                      | (a,i) ->
                          let uu____17320 = norm cfg env [] a  in
                          (uu____17320, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___116_17338  ->
                       match uu___116_17338 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17342 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17342
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___203_17350 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___204_17353 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___204_17353.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___203_17350.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___203_17350.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17356  ->
        match uu____17356 with
        | (x,imp) ->
            let uu____17359 =
              let uu___205_17360 = x  in
              let uu____17361 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___205_17360.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___205_17360.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17361
              }  in
            (uu____17359, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17367 =
          FStar_List.fold_left
            (fun uu____17385  ->
               fun b  ->
                 match uu____17385 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17367 with | (nbs,uu____17425) -> FStar_List.rev nbs

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
            let uu____17441 =
              let uu___206_17442 = rc  in
              let uu____17443 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___206_17442.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17443;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___206_17442.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17441
        | uu____17450 -> lopt

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
            (let uu____17471 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17472 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____17471
               uu____17472)
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
          let uu____17492 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____17492
          then tm1
          else
            (let w t =
               let uu___207_17506 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___207_17506.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___207_17506.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17517 =
                 let uu____17518 = FStar_Syntax_Util.unmeta t  in
                 uu____17518.FStar_Syntax_Syntax.n  in
               match uu____17517 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17525 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17574)::args1,(bv,uu____17577)::bs1) ->
                   let uu____17611 =
                     let uu____17612 = FStar_Syntax_Subst.compress t  in
                     uu____17612.FStar_Syntax_Syntax.n  in
                   (match uu____17611 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17616 -> false)
               | ([],[]) -> true
               | (uu____17637,uu____17638) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____17679 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17680 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____17679
                    uu____17680)
               else ();
               (let uu____17682 = FStar_Syntax_Util.head_and_args' t  in
                match uu____17682 with
                | (hd1,args) ->
                    let uu____17715 =
                      let uu____17716 = FStar_Syntax_Subst.compress hd1  in
                      uu____17716.FStar_Syntax_Syntax.n  in
                    (match uu____17715 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____17723 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____17724 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____17725 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____17723 uu____17724 uu____17725)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____17727 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____17744 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17745 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____17744
                    uu____17745)
               else ();
               (let uu____17747 = FStar_Syntax_Util.is_squash t  in
                match uu____17747 with
                | FStar_Pervasives_Native.Some (uu____17758,t') ->
                    is_applied bs t'
                | uu____17770 ->
                    let uu____17779 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____17779 with
                     | FStar_Pervasives_Native.Some (uu____17790,t') ->
                         is_applied bs t'
                     | uu____17802 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____17826 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17826 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____17833)::(q,uu____17835)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____17871 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____17872 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____17871 uu____17872)
                    else ();
                    (let uu____17874 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____17874 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____17879 =
                           let uu____17880 = FStar_Syntax_Subst.compress p
                              in
                           uu____17880.FStar_Syntax_Syntax.n  in
                         (match uu____17879 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____17888 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____17888))
                          | uu____17889 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____17892)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____17917 =
                           let uu____17918 = FStar_Syntax_Subst.compress p1
                              in
                           uu____17918.FStar_Syntax_Syntax.n  in
                         (match uu____17917 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____17926 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____17926))
                          | uu____17927 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____17931 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____17931 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____17936 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____17936 with
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
                                     let uu____17945 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____17945))
                               | uu____17946 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____17951)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____17976 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____17976 with
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
                                     let uu____17985 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____17985))
                               | uu____17986 -> FStar_Pervasives_Native.None)
                          | uu____17989 -> FStar_Pervasives_Native.None)
                     | uu____17992 -> FStar_Pervasives_Native.None))
               | uu____17995 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18008 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18008 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18014)::[],uu____18015,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____18032 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18033 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18032
                         uu____18033)
                    else ();
                    is_quantified_const bv phi')
               | uu____18035 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18048 =
                 let uu____18049 = FStar_Syntax_Subst.compress phi  in
                 uu____18049.FStar_Syntax_Syntax.n  in
               match uu____18048 with
               | FStar_Syntax_Syntax.Tm_match (uu____18054,br::brs) ->
                   let uu____18121 = br  in
                   (match uu____18121 with
                    | (uu____18138,uu____18139,e) ->
                        let r =
                          let uu____18160 = simp_t e  in
                          match uu____18160 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18166 =
                                FStar_List.for_all
                                  (fun uu____18184  ->
                                     match uu____18184 with
                                     | (uu____18197,uu____18198,e') ->
                                         let uu____18212 = simp_t e'  in
                                         uu____18212 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18166
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18220 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18227 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18227
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18252 =
                 match uu____18252 with
                 | (t1,q) ->
                     let uu____18265 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18265 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18293 -> (t1, q))
                  in
               let uu____18302 = FStar_Syntax_Util.head_and_args t  in
               match uu____18302 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18366 =
                 let uu____18367 = FStar_Syntax_Util.unmeta ty  in
                 uu____18367.FStar_Syntax_Syntax.n  in
               match uu____18366 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18371) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18376,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18396 -> false  in
             let simplify1 arg =
               let uu____18421 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18421, arg)  in
             let uu____18430 = is_forall_const tm1  in
             match uu____18430 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____18435 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____18436 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18435
                       uu____18436)
                  else ();
                  (let uu____18438 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____18438))
             | FStar_Pervasives_Native.None  ->
                 let uu____18439 =
                   let uu____18440 = FStar_Syntax_Subst.compress tm1  in
                   uu____18440.FStar_Syntax_Syntax.n  in
                 (match uu____18439 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18444;
                              FStar_Syntax_Syntax.vars = uu____18445;_},uu____18446);
                         FStar_Syntax_Syntax.pos = uu____18447;
                         FStar_Syntax_Syntax.vars = uu____18448;_},args)
                      ->
                      let uu____18474 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18474
                      then
                        let uu____18475 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18475 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18522)::
                             (uu____18523,(arg,uu____18525))::[] ->
                             maybe_auto_squash arg
                         | (uu____18574,(arg,uu____18576))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18577)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18626)::uu____18627::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18678::(FStar_Pervasives_Native.Some (false
                                         ),uu____18679)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18730 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18744 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18744
                         then
                           let uu____18745 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18745 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18792)::uu____18793::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18844::(FStar_Pervasives_Native.Some (true
                                           ),uu____18845)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18896)::(uu____18897,(arg,uu____18899))::[]
                               -> maybe_auto_squash arg
                           | (uu____18948,(arg,uu____18950))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18951)::[]
                               -> maybe_auto_squash arg
                           | uu____19000 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19014 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19014
                            then
                              let uu____19015 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19015 with
                              | uu____19062::(FStar_Pervasives_Native.Some
                                              (true ),uu____19063)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19114)::uu____19115::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19166)::(uu____19167,(arg,uu____19169))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19218,(p,uu____19220))::(uu____19221,
                                                                (q,uu____19223))::[]
                                  ->
                                  let uu____19270 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19270
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19272 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19286 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19286
                               then
                                 let uu____19287 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19287 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19334)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19335)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19386)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19387)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19438)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19439)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19490)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19491)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19542,(arg,uu____19544))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19545)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19594)::(uu____19595,(arg,uu____19597))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19646,(arg,uu____19648))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19649)::[]
                                     ->
                                     let uu____19698 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19698
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19699)::(uu____19700,(arg,uu____19702))::[]
                                     ->
                                     let uu____19751 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19751
                                 | (uu____19752,(p,uu____19754))::(uu____19755,
                                                                   (q,uu____19757))::[]
                                     ->
                                     let uu____19804 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19804
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19806 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19820 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19820
                                  then
                                    let uu____19821 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19821 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19868)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19899)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19930 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19944 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19944
                                     then
                                       match args with
                                       | (t,uu____19946)::[] ->
                                           let uu____19963 =
                                             let uu____19964 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19964.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19963 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19967::[],body,uu____19969)
                                                ->
                                                let uu____19996 = simp_t body
                                                   in
                                                (match uu____19996 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19999 -> tm1)
                                            | uu____20002 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20004))::(t,uu____20006)::[]
                                           ->
                                           let uu____20045 =
                                             let uu____20046 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20046.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20045 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20049::[],body,uu____20051)
                                                ->
                                                let uu____20078 = simp_t body
                                                   in
                                                (match uu____20078 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20081 -> tm1)
                                            | uu____20084 -> tm1)
                                       | uu____20085 -> tm1
                                     else
                                       (let uu____20095 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20095
                                        then
                                          match args with
                                          | (t,uu____20097)::[] ->
                                              let uu____20114 =
                                                let uu____20115 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20115.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20114 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20118::[],body,uu____20120)
                                                   ->
                                                   let uu____20147 =
                                                     simp_t body  in
                                                   (match uu____20147 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20150 -> tm1)
                                               | uu____20153 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20155))::(t,uu____20157)::[]
                                              ->
                                              let uu____20196 =
                                                let uu____20197 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20197.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20196 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20200::[],body,uu____20202)
                                                   ->
                                                   let uu____20229 =
                                                     simp_t body  in
                                                   (match uu____20229 with
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
                                                    | uu____20232 -> tm1)
                                               | uu____20235 -> tm1)
                                          | uu____20236 -> tm1
                                        else
                                          (let uu____20246 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20246
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20247;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20248;_},uu____20249)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20266;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20267;_},uu____20268)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20285 -> tm1
                                           else
                                             (let uu____20295 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20295 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20315 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20325;
                         FStar_Syntax_Syntax.vars = uu____20326;_},args)
                      ->
                      let uu____20348 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20348
                      then
                        let uu____20349 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20349 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20396)::
                             (uu____20397,(arg,uu____20399))::[] ->
                             maybe_auto_squash arg
                         | (uu____20448,(arg,uu____20450))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20451)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20500)::uu____20501::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20552::(FStar_Pervasives_Native.Some (false
                                         ),uu____20553)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20604 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20618 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20618
                         then
                           let uu____20619 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20619 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____20666)::uu____20667::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____20718::(FStar_Pervasives_Native.Some (true
                                           ),uu____20719)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____20770)::(uu____20771,(arg,uu____20773))::[]
                               -> maybe_auto_squash arg
                           | (uu____20822,(arg,uu____20824))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____20825)::[]
                               -> maybe_auto_squash arg
                           | uu____20874 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____20888 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____20888
                            then
                              let uu____20889 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____20889 with
                              | uu____20936::(FStar_Pervasives_Native.Some
                                              (true ),uu____20937)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____20988)::uu____20989::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21040)::(uu____21041,(arg,uu____21043))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21092,(p,uu____21094))::(uu____21095,
                                                                (q,uu____21097))::[]
                                  ->
                                  let uu____21144 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21144
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21146 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21160 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21160
                               then
                                 let uu____21161 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21161 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21208)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21209)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21260)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21261)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21312)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21313)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21364)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21365)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21416,(arg,uu____21418))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21419)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21468)::(uu____21469,(arg,uu____21471))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21520,(arg,uu____21522))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21523)::[]
                                     ->
                                     let uu____21572 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21572
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21573)::(uu____21574,(arg,uu____21576))::[]
                                     ->
                                     let uu____21625 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21625
                                 | (uu____21626,(p,uu____21628))::(uu____21629,
                                                                   (q,uu____21631))::[]
                                     ->
                                     let uu____21678 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21678
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21680 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21694 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____21694
                                  then
                                    let uu____21695 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____21695 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____21742)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21773)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21804 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21818 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21818
                                     then
                                       match args with
                                       | (t,uu____21820)::[] ->
                                           let uu____21837 =
                                             let uu____21838 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21838.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21837 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21841::[],body,uu____21843)
                                                ->
                                                let uu____21870 = simp_t body
                                                   in
                                                (match uu____21870 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21873 -> tm1)
                                            | uu____21876 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21878))::(t,uu____21880)::[]
                                           ->
                                           let uu____21919 =
                                             let uu____21920 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21920.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21919 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21923::[],body,uu____21925)
                                                ->
                                                let uu____21952 = simp_t body
                                                   in
                                                (match uu____21952 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21955 -> tm1)
                                            | uu____21958 -> tm1)
                                       | uu____21959 -> tm1
                                     else
                                       (let uu____21969 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21969
                                        then
                                          match args with
                                          | (t,uu____21971)::[] ->
                                              let uu____21988 =
                                                let uu____21989 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21989.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21988 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21992::[],body,uu____21994)
                                                   ->
                                                   let uu____22021 =
                                                     simp_t body  in
                                                   (match uu____22021 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22024 -> tm1)
                                               | uu____22027 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22029))::(t,uu____22031)::[]
                                              ->
                                              let uu____22070 =
                                                let uu____22071 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22071.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22070 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22074::[],body,uu____22076)
                                                   ->
                                                   let uu____22103 =
                                                     simp_t body  in
                                                   (match uu____22103 with
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
                                                    | uu____22106 -> tm1)
                                               | uu____22109 -> tm1)
                                          | uu____22110 -> tm1
                                        else
                                          (let uu____22120 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22120
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22121;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22122;_},uu____22123)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22140;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22141;_},uu____22142)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22159 -> tm1
                                           else
                                             (let uu____22169 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22169 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22189 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____22204 = simp_t t  in
                      (match uu____22204 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22207 ->
                      let uu____22230 = is_const_match tm1  in
                      (match uu____22230 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____22233 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____22243  ->
               (let uu____22245 = FStar_Syntax_Print.tag_of_term t  in
                let uu____22246 = FStar_Syntax_Print.term_to_string t  in
                let uu____22247 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____22254 =
                  let uu____22255 =
                    let uu____22258 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____22258
                     in
                  stack_to_string uu____22255  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____22245 uu____22246 uu____22247 uu____22254);
               (let uu____22281 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____22281
                then
                  let uu____22282 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____22282 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____22289 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____22290 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____22291 =
                          let uu____22292 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____22292
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____22289
                          uu____22290 uu____22291);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____22310 =
                     let uu____22311 =
                       let uu____22312 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____22312  in
                     FStar_Util.string_of_int uu____22311  in
                   let uu____22317 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____22318 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____22310 uu____22317 uu____22318)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____22324,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____22373  ->
                     let uu____22374 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____22374);
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
               let uu____22410 =
                 let uu___208_22411 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___208_22411.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___208_22411.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____22410
           | (Arg (Univ uu____22412,uu____22413,uu____22414))::uu____22415 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____22418,uu____22419))::uu____22420 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____22435,uu____22436),aq,r))::stack1
               when
               let uu____22486 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____22486 ->
               let t2 =
                 let uu____22490 =
                   let uu____22495 =
                     let uu____22496 = closure_as_term cfg env_arg tm  in
                     (uu____22496, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____22495  in
                 uu____22490 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____22502),aq,r))::stack1 ->
               (log cfg
                  (fun uu____22555  ->
                     let uu____22556 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____22556);
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
                  (let uu____22566 = FStar_ST.op_Bang m  in
                   match uu____22566 with
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
                   | FStar_Pervasives_Native.Some (uu____22707,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____22758 =
                 log cfg
                   (fun uu____22762  ->
                      let uu____22763 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____22763);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____22767 =
                 let uu____22768 = FStar_Syntax_Subst.compress t1  in
                 uu____22768.FStar_Syntax_Syntax.n  in
               (match uu____22767 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____22795 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____22795  in
                    (log cfg
                       (fun uu____22799  ->
                          let uu____22800 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____22800);
                     (let uu____22801 = FStar_List.tl stack  in
                      norm cfg env1 uu____22801 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____22802);
                       FStar_Syntax_Syntax.pos = uu____22803;
                       FStar_Syntax_Syntax.vars = uu____22804;_},(e,uu____22806)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____22835 when
                    (cfg.steps).primops ->
                    let uu____22850 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____22850 with
                     | (hd1,args) ->
                         let uu____22887 =
                           let uu____22888 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____22888.FStar_Syntax_Syntax.n  in
                         (match uu____22887 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____22892 = find_prim_step cfg fv  in
                              (match uu____22892 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____22895; arity = uu____22896;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____22898;
                                     requires_binder_substitution =
                                       uu____22899;
                                     interpretation = uu____22900;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____22915 -> fallback " (3)" ())
                          | uu____22918 -> fallback " (4)" ()))
                | uu____22919 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____22940  ->
                     let uu____22941 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____22941);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____22950 =
                   log cfg1
                     (fun uu____22955  ->
                        let uu____22956 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____22957 =
                          let uu____22958 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____22975  ->
                                    match uu____22975 with
                                    | (p,uu____22985,uu____22986) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____22958
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____22956 uu____22957);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___117_23003  ->
                                match uu___117_23003 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____23004 -> false))
                         in
                      let steps =
                        let uu___209_23006 = cfg1.steps  in
                        {
                          beta = (uu___209_23006.beta);
                          iota = (uu___209_23006.iota);
                          zeta = false;
                          weak = (uu___209_23006.weak);
                          hnf = (uu___209_23006.hnf);
                          primops = (uu___209_23006.primops);
                          do_not_unfold_pure_lets =
                            (uu___209_23006.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___209_23006.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___209_23006.pure_subterms_within_computations);
                          simplify = (uu___209_23006.simplify);
                          erase_universes = (uu___209_23006.erase_universes);
                          allow_unbound_universes =
                            (uu___209_23006.allow_unbound_universes);
                          reify_ = (uu___209_23006.reify_);
                          compress_uvars = (uu___209_23006.compress_uvars);
                          no_full_norm = (uu___209_23006.no_full_norm);
                          check_no_uvars = (uu___209_23006.check_no_uvars);
                          unmeta = (uu___209_23006.unmeta);
                          unascribe = (uu___209_23006.unascribe);
                          in_full_norm_request =
                            (uu___209_23006.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___209_23006.weakly_reduce_scrutinee)
                        }  in
                      let uu___210_23011 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___210_23011.tcenv);
                        debug = (uu___210_23011.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___210_23011.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___210_23011.memoize_lazy);
                        normalize_pure_lets =
                          (uu___210_23011.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____23051 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____23072 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____23132  ->
                                    fun uu____23133  ->
                                      match (uu____23132, uu____23133) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____23224 = norm_pat env3 p1
                                             in
                                          (match uu____23224 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____23072 with
                           | (pats1,env3) ->
                               ((let uu___211_23306 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___211_23306.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___212_23325 = x  in
                            let uu____23326 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___212_23325.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___212_23325.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23326
                            }  in
                          ((let uu___213_23340 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___213_23340.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___214_23351 = x  in
                            let uu____23352 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___214_23351.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___214_23351.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23352
                            }  in
                          ((let uu___215_23366 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___215_23366.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___216_23382 = x  in
                            let uu____23383 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___216_23382.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___216_23382.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23383
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___217_23390 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___217_23390.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____23400 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____23414 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____23414 with
                                  | (p,wopt,e) ->
                                      let uu____23434 = norm_pat env1 p  in
                                      (match uu____23434 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____23459 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____23459
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____23466 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____23466
                      then
                        norm
                          (let uu___218_23469 = cfg1  in
                           {
                             steps =
                               (let uu___219_23472 = cfg1.steps  in
                                {
                                  beta = (uu___219_23472.beta);
                                  iota = (uu___219_23472.iota);
                                  zeta = (uu___219_23472.zeta);
                                  weak = (uu___219_23472.weak);
                                  hnf = (uu___219_23472.hnf);
                                  primops = (uu___219_23472.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___219_23472.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___219_23472.unfold_until);
                                  unfold_only = (uu___219_23472.unfold_only);
                                  unfold_fully =
                                    (uu___219_23472.unfold_fully);
                                  unfold_attr = (uu___219_23472.unfold_attr);
                                  unfold_tac = (uu___219_23472.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___219_23472.pure_subterms_within_computations);
                                  simplify = (uu___219_23472.simplify);
                                  erase_universes =
                                    (uu___219_23472.erase_universes);
                                  allow_unbound_universes =
                                    (uu___219_23472.allow_unbound_universes);
                                  reify_ = (uu___219_23472.reify_);
                                  compress_uvars =
                                    (uu___219_23472.compress_uvars);
                                  no_full_norm =
                                    (uu___219_23472.no_full_norm);
                                  check_no_uvars =
                                    (uu___219_23472.check_no_uvars);
                                  unmeta = (uu___219_23472.unmeta);
                                  unascribe = (uu___219_23472.unascribe);
                                  in_full_norm_request =
                                    (uu___219_23472.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___218_23469.tcenv);
                             debug = (uu___218_23469.debug);
                             delta_level = (uu___218_23469.delta_level);
                             primitive_steps =
                               (uu___218_23469.primitive_steps);
                             strong = (uu___218_23469.strong);
                             memoize_lazy = (uu___218_23469.memoize_lazy);
                             normalize_pure_lets =
                               (uu___218_23469.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____23474 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____23474)
                    in
                 let rec is_cons head1 =
                   let uu____23481 =
                     let uu____23482 = FStar_Syntax_Subst.compress head1  in
                     uu____23482.FStar_Syntax_Syntax.n  in
                   match uu____23481 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____23486) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____23491 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____23492;
                         FStar_Syntax_Syntax.fv_delta = uu____23493;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____23494;
                         FStar_Syntax_Syntax.fv_delta = uu____23495;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____23496);_}
                       -> true
                   | uu____23503 -> false  in
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
                   let uu____23664 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____23664 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____23751 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____23790 ->
                                 let uu____23791 =
                                   let uu____23792 = is_cons head1  in
                                   Prims.op_Negation uu____23792  in
                                 FStar_Util.Inr uu____23791)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____23817 =
                              let uu____23818 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____23818.FStar_Syntax_Syntax.n  in
                            (match uu____23817 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____23836 ->
                                 let uu____23837 =
                                   let uu____23838 = is_cons head1  in
                                   Prims.op_Negation uu____23838  in
                                 FStar_Util.Inr uu____23837))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____23907)::rest_a,(p1,uu____23910)::rest_p) ->
                       let uu____23954 = matches_pat t2 p1  in
                       (match uu____23954 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____24003 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____24113 = matches_pat scrutinee1 p1  in
                       (match uu____24113 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____24153  ->
                                  let uu____24154 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____24155 =
                                    let uu____24156 =
                                      FStar_List.map
                                        (fun uu____24166  ->
                                           match uu____24166 with
                                           | (uu____24171,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____24156
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____24154 uu____24155);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____24203  ->
                                       match uu____24203 with
                                       | (bv,t2) ->
                                           let uu____24226 =
                                             let uu____24233 =
                                               let uu____24236 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____24236
                                                in
                                             let uu____24237 =
                                               let uu____24238 =
                                                 let uu____24269 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____24269, false)
                                                  in
                                               Clos uu____24238  in
                                             (uu____24233, uu____24237)  in
                                           uu____24226 :: env2) env1 s
                                 in
                              let uu____24386 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____24386)))
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
    let uu____24413 =
      let uu____24416 = FStar_ST.op_Bang plugins  in p :: uu____24416  in
    FStar_ST.op_Colon_Equals plugins uu____24413  in
  let retrieve uu____24524 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____24601  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___118_24642  ->
                  match uu___118_24642 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____24646 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____24652 -> d  in
        let uu____24655 = to_fsteps s  in
        let uu____24656 =
          let uu____24657 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____24658 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____24659 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____24660 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____24661 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____24662 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____24657;
            primop = uu____24658;
            b380 = uu____24659;
            wpe = uu____24660;
            norm_delayed = uu____24661;
            print_normalized = uu____24662
          }  in
        let uu____24663 =
          let uu____24666 =
            let uu____24669 = retrieve_plugins ()  in
            FStar_List.append uu____24669 psteps  in
          add_steps built_in_primitive_steps uu____24666  in
        let uu____24672 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____24674 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____24674)
           in
        {
          steps = uu____24655;
          tcenv = e;
          debug = uu____24656;
          delta_level = d1;
          primitive_steps = uu____24663;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____24672
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
      fun t  -> let uu____24756 = config s e  in norm_comp uu____24756 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____24773 = config [] env  in norm_universe uu____24773 [] u
  
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
        let uu____24797 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24797  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____24804 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___220_24823 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___220_24823.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___220_24823.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____24830 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____24830
          then
            let ct1 =
              let uu____24832 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____24832 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____24839 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____24839
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___221_24843 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___221_24843.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___221_24843.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___221_24843.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___222_24845 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___222_24845.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___222_24845.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___222_24845.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___222_24845.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___223_24846 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___223_24846.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___223_24846.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____24848 -> c
  
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
        let uu____24866 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24866  in
      let uu____24873 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____24873
      then
        let uu____24874 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____24874 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____24880  ->
                 let uu____24881 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____24881)
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
            ((let uu____24902 =
                let uu____24907 =
                  let uu____24908 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____24908
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____24907)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____24902);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____24923 = config [AllowUnboundUniverses] env  in
          norm_comp uu____24923 [] c
        with
        | e ->
            ((let uu____24936 =
                let uu____24941 =
                  let uu____24942 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____24942
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____24941)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____24936);
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
                   let uu____24987 =
                     let uu____24988 =
                       let uu____24995 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____24995)  in
                     FStar_Syntax_Syntax.Tm_refine uu____24988  in
                   mk uu____24987 t01.FStar_Syntax_Syntax.pos
               | uu____25000 -> t2)
          | uu____25001 -> t2  in
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
        let uu____25065 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____25065 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____25094 ->
                 let uu____25101 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____25101 with
                  | (actuals,uu____25111,uu____25112) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____25126 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____25126 with
                         | (binders,args) ->
                             let uu____25143 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____25143
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
      | uu____25155 ->
          let uu____25156 = FStar_Syntax_Util.head_and_args t  in
          (match uu____25156 with
           | (head1,args) ->
               let uu____25193 =
                 let uu____25194 = FStar_Syntax_Subst.compress head1  in
                 uu____25194.FStar_Syntax_Syntax.n  in
               (match uu____25193 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____25197,thead) ->
                    let uu____25223 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____25223 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____25265 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___228_25273 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___228_25273.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___228_25273.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___228_25273.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___228_25273.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___228_25273.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___228_25273.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___228_25273.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___228_25273.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___228_25273.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___228_25273.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___228_25273.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___228_25273.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___228_25273.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___228_25273.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___228_25273.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___228_25273.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___228_25273.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___228_25273.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___228_25273.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___228_25273.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___228_25273.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___228_25273.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___228_25273.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___228_25273.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___228_25273.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___228_25273.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___228_25273.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___228_25273.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___228_25273.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___228_25273.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___228_25273.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___228_25273.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___228_25273.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___228_25273.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____25265 with
                            | (uu____25274,ty,uu____25276) ->
                                eta_expand_with_type env t ty))
                | uu____25277 ->
                    let uu____25278 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___229_25286 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___229_25286.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___229_25286.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___229_25286.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___229_25286.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___229_25286.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___229_25286.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___229_25286.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___229_25286.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___229_25286.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___229_25286.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___229_25286.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___229_25286.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___229_25286.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___229_25286.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___229_25286.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___229_25286.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___229_25286.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___229_25286.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___229_25286.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___229_25286.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___229_25286.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___229_25286.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___229_25286.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___229_25286.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___229_25286.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___229_25286.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___229_25286.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___229_25286.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___229_25286.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___229_25286.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___229_25286.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___229_25286.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___229_25286.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___229_25286.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____25278 with
                     | (uu____25287,ty,uu____25289) ->
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
      let uu___230_25362 = x  in
      let uu____25363 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___230_25362.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___230_25362.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____25363
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____25366 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____25391 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____25392 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____25393 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____25394 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____25401 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____25402 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____25403 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___231_25433 = rc  in
          let uu____25434 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____25441 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___231_25433.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____25434;
            FStar_Syntax_Syntax.residual_flags = uu____25441
          }  in
        let uu____25444 =
          let uu____25445 =
            let uu____25462 = elim_delayed_subst_binders bs  in
            let uu____25469 = elim_delayed_subst_term t2  in
            let uu____25470 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____25462, uu____25469, uu____25470)  in
          FStar_Syntax_Syntax.Tm_abs uu____25445  in
        mk1 uu____25444
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____25499 =
          let uu____25500 =
            let uu____25513 = elim_delayed_subst_binders bs  in
            let uu____25520 = elim_delayed_subst_comp c  in
            (uu____25513, uu____25520)  in
          FStar_Syntax_Syntax.Tm_arrow uu____25500  in
        mk1 uu____25499
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____25533 =
          let uu____25534 =
            let uu____25541 = elim_bv bv  in
            let uu____25542 = elim_delayed_subst_term phi  in
            (uu____25541, uu____25542)  in
          FStar_Syntax_Syntax.Tm_refine uu____25534  in
        mk1 uu____25533
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____25565 =
          let uu____25566 =
            let uu____25581 = elim_delayed_subst_term t2  in
            let uu____25582 = elim_delayed_subst_args args  in
            (uu____25581, uu____25582)  in
          FStar_Syntax_Syntax.Tm_app uu____25566  in
        mk1 uu____25565
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___232_25648 = p  in
              let uu____25649 =
                let uu____25650 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____25650  in
              {
                FStar_Syntax_Syntax.v = uu____25649;
                FStar_Syntax_Syntax.p =
                  (uu___232_25648.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___233_25652 = p  in
              let uu____25653 =
                let uu____25654 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____25654  in
              {
                FStar_Syntax_Syntax.v = uu____25653;
                FStar_Syntax_Syntax.p =
                  (uu___233_25652.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___234_25661 = p  in
              let uu____25662 =
                let uu____25663 =
                  let uu____25670 = elim_bv x  in
                  let uu____25671 = elim_delayed_subst_term t0  in
                  (uu____25670, uu____25671)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____25663  in
              {
                FStar_Syntax_Syntax.v = uu____25662;
                FStar_Syntax_Syntax.p =
                  (uu___234_25661.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___235_25690 = p  in
              let uu____25691 =
                let uu____25692 =
                  let uu____25705 =
                    FStar_List.map
                      (fun uu____25728  ->
                         match uu____25728 with
                         | (x,b) ->
                             let uu____25741 = elim_pat x  in
                             (uu____25741, b)) pats
                     in
                  (fv, uu____25705)  in
                FStar_Syntax_Syntax.Pat_cons uu____25692  in
              {
                FStar_Syntax_Syntax.v = uu____25691;
                FStar_Syntax_Syntax.p =
                  (uu___235_25690.FStar_Syntax_Syntax.p)
              }
          | uu____25754 -> p  in
        let elim_branch uu____25778 =
          match uu____25778 with
          | (pat,wopt,t3) ->
              let uu____25804 = elim_pat pat  in
              let uu____25807 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____25810 = elim_delayed_subst_term t3  in
              (uu____25804, uu____25807, uu____25810)
           in
        let uu____25815 =
          let uu____25816 =
            let uu____25839 = elim_delayed_subst_term t2  in
            let uu____25840 = FStar_List.map elim_branch branches  in
            (uu____25839, uu____25840)  in
          FStar_Syntax_Syntax.Tm_match uu____25816  in
        mk1 uu____25815
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____25951 =
          match uu____25951 with
          | (tc,topt) ->
              let uu____25986 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____25996 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____25996
                | FStar_Util.Inr c ->
                    let uu____25998 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____25998
                 in
              let uu____25999 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____25986, uu____25999)
           in
        let uu____26008 =
          let uu____26009 =
            let uu____26036 = elim_delayed_subst_term t2  in
            let uu____26037 = elim_ascription a  in
            (uu____26036, uu____26037, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____26009  in
        mk1 uu____26008
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___236_26084 = lb  in
          let uu____26085 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____26088 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___236_26084.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___236_26084.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____26085;
            FStar_Syntax_Syntax.lbeff =
              (uu___236_26084.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____26088;
            FStar_Syntax_Syntax.lbattrs =
              (uu___236_26084.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___236_26084.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____26091 =
          let uu____26092 =
            let uu____26105 =
              let uu____26112 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____26112)  in
            let uu____26121 = elim_delayed_subst_term t2  in
            (uu____26105, uu____26121)  in
          FStar_Syntax_Syntax.Tm_let uu____26092  in
        mk1 uu____26091
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____26154 =
          let uu____26155 =
            let uu____26172 = elim_delayed_subst_term t2  in
            (uv, uu____26172)  in
          FStar_Syntax_Syntax.Tm_uvar uu____26155  in
        mk1 uu____26154
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____26190 =
          let uu____26191 =
            let uu____26198 = elim_delayed_subst_term tm  in
            (uu____26198, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____26191  in
        mk1 uu____26190
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____26205 =
          let uu____26206 =
            let uu____26213 = elim_delayed_subst_term t2  in
            let uu____26214 = elim_delayed_subst_meta md  in
            (uu____26213, uu____26214)  in
          FStar_Syntax_Syntax.Tm_meta uu____26206  in
        mk1 uu____26205

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___119_26221  ->
         match uu___119_26221 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____26225 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____26225
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
        let uu____26248 =
          let uu____26249 =
            let uu____26258 = elim_delayed_subst_term t  in
            (uu____26258, uopt)  in
          FStar_Syntax_Syntax.Total uu____26249  in
        mk1 uu____26248
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____26271 =
          let uu____26272 =
            let uu____26281 = elim_delayed_subst_term t  in
            (uu____26281, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____26272  in
        mk1 uu____26271
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___237_26286 = ct  in
          let uu____26287 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____26290 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____26299 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___237_26286.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___237_26286.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____26287;
            FStar_Syntax_Syntax.effect_args = uu____26290;
            FStar_Syntax_Syntax.flags = uu____26299
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___120_26302  ->
    match uu___120_26302 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____26314 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____26314
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____26347 =
          let uu____26354 = elim_delayed_subst_term t  in (m, uu____26354)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____26347
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____26362 =
          let uu____26371 = elim_delayed_subst_term t  in
          (m1, m2, uu____26371)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____26362
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____26394  ->
         match uu____26394 with
         | (t,q) ->
             let uu____26405 = elim_delayed_subst_term t  in (uu____26405, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____26425  ->
         match uu____26425 with
         | (x,q) ->
             let uu____26436 =
               let uu___238_26437 = x  in
               let uu____26438 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___238_26437.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___238_26437.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____26438
               }  in
             (uu____26436, q)) bs

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
            | (uu____26522,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____26528,FStar_Util.Inl t) ->
                let uu____26534 =
                  let uu____26541 =
                    let uu____26542 =
                      let uu____26555 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____26555)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____26542  in
                  FStar_Syntax_Syntax.mk uu____26541  in
                uu____26534 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____26559 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____26559 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____26587 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____26642 ->
                    let uu____26643 =
                      let uu____26652 =
                        let uu____26653 = FStar_Syntax_Subst.compress t4  in
                        uu____26653.FStar_Syntax_Syntax.n  in
                      (uu____26652, tc)  in
                    (match uu____26643 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____26678) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____26715) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____26754,FStar_Util.Inl uu____26755) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____26778 -> failwith "Impossible")
                 in
              (match uu____26587 with
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
          let uu____26891 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____26891 with
          | (univ_names1,binders1,tc) ->
              let uu____26949 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____26949)
  
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
          let uu____26992 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____26992 with
          | (univ_names1,binders1,tc) ->
              let uu____27052 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____27052)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____27089 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____27089 with
           | (univ_names1,binders1,typ1) ->
               let uu___239_27117 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___239_27117.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___239_27117.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___239_27117.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___239_27117.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___240_27138 = s  in
          let uu____27139 =
            let uu____27140 =
              let uu____27149 = FStar_List.map (elim_uvars env) sigs  in
              (uu____27149, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____27140  in
          {
            FStar_Syntax_Syntax.sigel = uu____27139;
            FStar_Syntax_Syntax.sigrng =
              (uu___240_27138.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___240_27138.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___240_27138.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___240_27138.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____27166 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27166 with
           | (univ_names1,uu____27184,typ1) ->
               let uu___241_27198 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___241_27198.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___241_27198.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___241_27198.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___241_27198.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____27204 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27204 with
           | (univ_names1,uu____27222,typ1) ->
               let uu___242_27236 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___242_27236.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___242_27236.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___242_27236.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___242_27236.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____27270 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____27270 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____27295 =
                            let uu____27296 =
                              let uu____27297 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____27297  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____27296
                             in
                          elim_delayed_subst_term uu____27295  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___243_27300 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___243_27300.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___243_27300.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___243_27300.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___243_27300.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___244_27301 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___244_27301.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___244_27301.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___244_27301.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___244_27301.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___245_27313 = s  in
          let uu____27314 =
            let uu____27315 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____27315  in
          {
            FStar_Syntax_Syntax.sigel = uu____27314;
            FStar_Syntax_Syntax.sigrng =
              (uu___245_27313.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___245_27313.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___245_27313.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___245_27313.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____27319 = elim_uvars_aux_t env us [] t  in
          (match uu____27319 with
           | (us1,uu____27337,t1) ->
               let uu___246_27351 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___246_27351.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___246_27351.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___246_27351.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___246_27351.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____27352 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____27354 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____27354 with
           | (univs1,binders,signature) ->
               let uu____27382 =
                 let uu____27391 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____27391 with
                 | (univs_opening,univs2) ->
                     let uu____27418 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____27418)
                  in
               (match uu____27382 with
                | (univs_opening,univs_closing) ->
                    let uu____27435 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____27441 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____27442 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____27441, uu____27442)  in
                    (match uu____27435 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____27466 =
                           match uu____27466 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____27484 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____27484 with
                                | (us1,t1) ->
                                    let uu____27495 =
                                      let uu____27500 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____27507 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____27500, uu____27507)  in
                                    (match uu____27495 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____27520 =
                                           let uu____27525 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____27534 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____27525, uu____27534)  in
                                         (match uu____27520 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____27550 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____27550
                                                 in
                                              let uu____27551 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____27551 with
                                               | (uu____27572,uu____27573,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____27588 =
                                                       let uu____27589 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____27589
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____27588
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____27596 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____27596 with
                           | (uu____27609,uu____27610,t1) -> t1  in
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
                             | uu____27672 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____27691 =
                               let uu____27692 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____27692.FStar_Syntax_Syntax.n  in
                             match uu____27691 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____27751 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____27782 =
                               let uu____27783 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____27783.FStar_Syntax_Syntax.n  in
                             match uu____27782 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____27804) ->
                                 let uu____27825 = destruct_action_body body
                                    in
                                 (match uu____27825 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____27870 ->
                                 let uu____27871 = destruct_action_body t  in
                                 (match uu____27871 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____27920 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____27920 with
                           | (action_univs,t) ->
                               let uu____27929 = destruct_action_typ_templ t
                                  in
                               (match uu____27929 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___247_27970 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___247_27970.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___247_27970.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___248_27972 = ed  in
                           let uu____27973 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____27974 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____27975 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____27976 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____27977 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____27978 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____27979 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____27980 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____27981 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____27982 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____27983 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____27984 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____27985 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____27986 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___248_27972.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___248_27972.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____27973;
                             FStar_Syntax_Syntax.bind_wp = uu____27974;
                             FStar_Syntax_Syntax.if_then_else = uu____27975;
                             FStar_Syntax_Syntax.ite_wp = uu____27976;
                             FStar_Syntax_Syntax.stronger = uu____27977;
                             FStar_Syntax_Syntax.close_wp = uu____27978;
                             FStar_Syntax_Syntax.assert_p = uu____27979;
                             FStar_Syntax_Syntax.assume_p = uu____27980;
                             FStar_Syntax_Syntax.null_wp = uu____27981;
                             FStar_Syntax_Syntax.trivial = uu____27982;
                             FStar_Syntax_Syntax.repr = uu____27983;
                             FStar_Syntax_Syntax.return_repr = uu____27984;
                             FStar_Syntax_Syntax.bind_repr = uu____27985;
                             FStar_Syntax_Syntax.actions = uu____27986;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___248_27972.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___249_27989 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___249_27989.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___249_27989.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___249_27989.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___249_27989.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___121_28008 =
            match uu___121_28008 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____28035 = elim_uvars_aux_t env us [] t  in
                (match uu____28035 with
                 | (us1,uu____28059,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___250_28078 = sub_eff  in
            let uu____28079 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____28082 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___250_28078.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___250_28078.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____28079;
              FStar_Syntax_Syntax.lift = uu____28082
            }  in
          let uu___251_28085 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___251_28085.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___251_28085.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___251_28085.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___251_28085.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____28095 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____28095 with
           | (univ_names1,binders1,comp1) ->
               let uu___252_28129 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___252_28129.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___252_28129.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___252_28129.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___252_28129.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____28140 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____28141 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  