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
      fun uu___79_269  ->
        match uu___79_269 with
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
      let add_opt x uu___80_1503 =
        match uu___80_1503 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___98_1523 = fs  in
          {
            beta = true;
            iota = (uu___98_1523.iota);
            zeta = (uu___98_1523.zeta);
            weak = (uu___98_1523.weak);
            hnf = (uu___98_1523.hnf);
            primops = (uu___98_1523.primops);
            do_not_unfold_pure_lets = (uu___98_1523.do_not_unfold_pure_lets);
            unfold_until = (uu___98_1523.unfold_until);
            unfold_only = (uu___98_1523.unfold_only);
            unfold_fully = (uu___98_1523.unfold_fully);
            unfold_attr = (uu___98_1523.unfold_attr);
            unfold_tac = (uu___98_1523.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1523.pure_subterms_within_computations);
            simplify = (uu___98_1523.simplify);
            erase_universes = (uu___98_1523.erase_universes);
            allow_unbound_universes = (uu___98_1523.allow_unbound_universes);
            reify_ = (uu___98_1523.reify_);
            compress_uvars = (uu___98_1523.compress_uvars);
            no_full_norm = (uu___98_1523.no_full_norm);
            check_no_uvars = (uu___98_1523.check_no_uvars);
            unmeta = (uu___98_1523.unmeta);
            unascribe = (uu___98_1523.unascribe);
            in_full_norm_request = (uu___98_1523.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___98_1523.weakly_reduce_scrutinee)
          }
      | Iota  ->
          let uu___99_1524 = fs  in
          {
            beta = (uu___99_1524.beta);
            iota = true;
            zeta = (uu___99_1524.zeta);
            weak = (uu___99_1524.weak);
            hnf = (uu___99_1524.hnf);
            primops = (uu___99_1524.primops);
            do_not_unfold_pure_lets = (uu___99_1524.do_not_unfold_pure_lets);
            unfold_until = (uu___99_1524.unfold_until);
            unfold_only = (uu___99_1524.unfold_only);
            unfold_fully = (uu___99_1524.unfold_fully);
            unfold_attr = (uu___99_1524.unfold_attr);
            unfold_tac = (uu___99_1524.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1524.pure_subterms_within_computations);
            simplify = (uu___99_1524.simplify);
            erase_universes = (uu___99_1524.erase_universes);
            allow_unbound_universes = (uu___99_1524.allow_unbound_universes);
            reify_ = (uu___99_1524.reify_);
            compress_uvars = (uu___99_1524.compress_uvars);
            no_full_norm = (uu___99_1524.no_full_norm);
            check_no_uvars = (uu___99_1524.check_no_uvars);
            unmeta = (uu___99_1524.unmeta);
            unascribe = (uu___99_1524.unascribe);
            in_full_norm_request = (uu___99_1524.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___99_1524.weakly_reduce_scrutinee)
          }
      | Zeta  ->
          let uu___100_1525 = fs  in
          {
            beta = (uu___100_1525.beta);
            iota = (uu___100_1525.iota);
            zeta = true;
            weak = (uu___100_1525.weak);
            hnf = (uu___100_1525.hnf);
            primops = (uu___100_1525.primops);
            do_not_unfold_pure_lets = (uu___100_1525.do_not_unfold_pure_lets);
            unfold_until = (uu___100_1525.unfold_until);
            unfold_only = (uu___100_1525.unfold_only);
            unfold_fully = (uu___100_1525.unfold_fully);
            unfold_attr = (uu___100_1525.unfold_attr);
            unfold_tac = (uu___100_1525.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1525.pure_subterms_within_computations);
            simplify = (uu___100_1525.simplify);
            erase_universes = (uu___100_1525.erase_universes);
            allow_unbound_universes = (uu___100_1525.allow_unbound_universes);
            reify_ = (uu___100_1525.reify_);
            compress_uvars = (uu___100_1525.compress_uvars);
            no_full_norm = (uu___100_1525.no_full_norm);
            check_no_uvars = (uu___100_1525.check_no_uvars);
            unmeta = (uu___100_1525.unmeta);
            unascribe = (uu___100_1525.unascribe);
            in_full_norm_request = (uu___100_1525.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___100_1525.weakly_reduce_scrutinee)
          }
      | Exclude (Beta ) ->
          let uu___101_1526 = fs  in
          {
            beta = false;
            iota = (uu___101_1526.iota);
            zeta = (uu___101_1526.zeta);
            weak = (uu___101_1526.weak);
            hnf = (uu___101_1526.hnf);
            primops = (uu___101_1526.primops);
            do_not_unfold_pure_lets = (uu___101_1526.do_not_unfold_pure_lets);
            unfold_until = (uu___101_1526.unfold_until);
            unfold_only = (uu___101_1526.unfold_only);
            unfold_fully = (uu___101_1526.unfold_fully);
            unfold_attr = (uu___101_1526.unfold_attr);
            unfold_tac = (uu___101_1526.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1526.pure_subterms_within_computations);
            simplify = (uu___101_1526.simplify);
            erase_universes = (uu___101_1526.erase_universes);
            allow_unbound_universes = (uu___101_1526.allow_unbound_universes);
            reify_ = (uu___101_1526.reify_);
            compress_uvars = (uu___101_1526.compress_uvars);
            no_full_norm = (uu___101_1526.no_full_norm);
            check_no_uvars = (uu___101_1526.check_no_uvars);
            unmeta = (uu___101_1526.unmeta);
            unascribe = (uu___101_1526.unascribe);
            in_full_norm_request = (uu___101_1526.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___101_1526.weakly_reduce_scrutinee)
          }
      | Exclude (Iota ) ->
          let uu___102_1527 = fs  in
          {
            beta = (uu___102_1527.beta);
            iota = false;
            zeta = (uu___102_1527.zeta);
            weak = (uu___102_1527.weak);
            hnf = (uu___102_1527.hnf);
            primops = (uu___102_1527.primops);
            do_not_unfold_pure_lets = (uu___102_1527.do_not_unfold_pure_lets);
            unfold_until = (uu___102_1527.unfold_until);
            unfold_only = (uu___102_1527.unfold_only);
            unfold_fully = (uu___102_1527.unfold_fully);
            unfold_attr = (uu___102_1527.unfold_attr);
            unfold_tac = (uu___102_1527.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1527.pure_subterms_within_computations);
            simplify = (uu___102_1527.simplify);
            erase_universes = (uu___102_1527.erase_universes);
            allow_unbound_universes = (uu___102_1527.allow_unbound_universes);
            reify_ = (uu___102_1527.reify_);
            compress_uvars = (uu___102_1527.compress_uvars);
            no_full_norm = (uu___102_1527.no_full_norm);
            check_no_uvars = (uu___102_1527.check_no_uvars);
            unmeta = (uu___102_1527.unmeta);
            unascribe = (uu___102_1527.unascribe);
            in_full_norm_request = (uu___102_1527.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___102_1527.weakly_reduce_scrutinee)
          }
      | Exclude (Zeta ) ->
          let uu___103_1528 = fs  in
          {
            beta = (uu___103_1528.beta);
            iota = (uu___103_1528.iota);
            zeta = false;
            weak = (uu___103_1528.weak);
            hnf = (uu___103_1528.hnf);
            primops = (uu___103_1528.primops);
            do_not_unfold_pure_lets = (uu___103_1528.do_not_unfold_pure_lets);
            unfold_until = (uu___103_1528.unfold_until);
            unfold_only = (uu___103_1528.unfold_only);
            unfold_fully = (uu___103_1528.unfold_fully);
            unfold_attr = (uu___103_1528.unfold_attr);
            unfold_tac = (uu___103_1528.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1528.pure_subterms_within_computations);
            simplify = (uu___103_1528.simplify);
            erase_universes = (uu___103_1528.erase_universes);
            allow_unbound_universes = (uu___103_1528.allow_unbound_universes);
            reify_ = (uu___103_1528.reify_);
            compress_uvars = (uu___103_1528.compress_uvars);
            no_full_norm = (uu___103_1528.no_full_norm);
            check_no_uvars = (uu___103_1528.check_no_uvars);
            unmeta = (uu___103_1528.unmeta);
            unascribe = (uu___103_1528.unascribe);
            in_full_norm_request = (uu___103_1528.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___103_1528.weakly_reduce_scrutinee)
          }
      | Exclude uu____1529 -> failwith "Bad exclude"
      | Weak  ->
          let uu___104_1530 = fs  in
          {
            beta = (uu___104_1530.beta);
            iota = (uu___104_1530.iota);
            zeta = (uu___104_1530.zeta);
            weak = true;
            hnf = (uu___104_1530.hnf);
            primops = (uu___104_1530.primops);
            do_not_unfold_pure_lets = (uu___104_1530.do_not_unfold_pure_lets);
            unfold_until = (uu___104_1530.unfold_until);
            unfold_only = (uu___104_1530.unfold_only);
            unfold_fully = (uu___104_1530.unfold_fully);
            unfold_attr = (uu___104_1530.unfold_attr);
            unfold_tac = (uu___104_1530.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1530.pure_subterms_within_computations);
            simplify = (uu___104_1530.simplify);
            erase_universes = (uu___104_1530.erase_universes);
            allow_unbound_universes = (uu___104_1530.allow_unbound_universes);
            reify_ = (uu___104_1530.reify_);
            compress_uvars = (uu___104_1530.compress_uvars);
            no_full_norm = (uu___104_1530.no_full_norm);
            check_no_uvars = (uu___104_1530.check_no_uvars);
            unmeta = (uu___104_1530.unmeta);
            unascribe = (uu___104_1530.unascribe);
            in_full_norm_request = (uu___104_1530.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___104_1530.weakly_reduce_scrutinee)
          }
      | HNF  ->
          let uu___105_1531 = fs  in
          {
            beta = (uu___105_1531.beta);
            iota = (uu___105_1531.iota);
            zeta = (uu___105_1531.zeta);
            weak = (uu___105_1531.weak);
            hnf = true;
            primops = (uu___105_1531.primops);
            do_not_unfold_pure_lets = (uu___105_1531.do_not_unfold_pure_lets);
            unfold_until = (uu___105_1531.unfold_until);
            unfold_only = (uu___105_1531.unfold_only);
            unfold_fully = (uu___105_1531.unfold_fully);
            unfold_attr = (uu___105_1531.unfold_attr);
            unfold_tac = (uu___105_1531.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1531.pure_subterms_within_computations);
            simplify = (uu___105_1531.simplify);
            erase_universes = (uu___105_1531.erase_universes);
            allow_unbound_universes = (uu___105_1531.allow_unbound_universes);
            reify_ = (uu___105_1531.reify_);
            compress_uvars = (uu___105_1531.compress_uvars);
            no_full_norm = (uu___105_1531.no_full_norm);
            check_no_uvars = (uu___105_1531.check_no_uvars);
            unmeta = (uu___105_1531.unmeta);
            unascribe = (uu___105_1531.unascribe);
            in_full_norm_request = (uu___105_1531.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___105_1531.weakly_reduce_scrutinee)
          }
      | Primops  ->
          let uu___106_1532 = fs  in
          {
            beta = (uu___106_1532.beta);
            iota = (uu___106_1532.iota);
            zeta = (uu___106_1532.zeta);
            weak = (uu___106_1532.weak);
            hnf = (uu___106_1532.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___106_1532.do_not_unfold_pure_lets);
            unfold_until = (uu___106_1532.unfold_until);
            unfold_only = (uu___106_1532.unfold_only);
            unfold_fully = (uu___106_1532.unfold_fully);
            unfold_attr = (uu___106_1532.unfold_attr);
            unfold_tac = (uu___106_1532.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1532.pure_subterms_within_computations);
            simplify = (uu___106_1532.simplify);
            erase_universes = (uu___106_1532.erase_universes);
            allow_unbound_universes = (uu___106_1532.allow_unbound_universes);
            reify_ = (uu___106_1532.reify_);
            compress_uvars = (uu___106_1532.compress_uvars);
            no_full_norm = (uu___106_1532.no_full_norm);
            check_no_uvars = (uu___106_1532.check_no_uvars);
            unmeta = (uu___106_1532.unmeta);
            unascribe = (uu___106_1532.unascribe);
            in_full_norm_request = (uu___106_1532.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___106_1532.weakly_reduce_scrutinee)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___107_1533 = fs  in
          {
            beta = (uu___107_1533.beta);
            iota = (uu___107_1533.iota);
            zeta = (uu___107_1533.zeta);
            weak = (uu___107_1533.weak);
            hnf = (uu___107_1533.hnf);
            primops = (uu___107_1533.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___107_1533.unfold_until);
            unfold_only = (uu___107_1533.unfold_only);
            unfold_fully = (uu___107_1533.unfold_fully);
            unfold_attr = (uu___107_1533.unfold_attr);
            unfold_tac = (uu___107_1533.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1533.pure_subterms_within_computations);
            simplify = (uu___107_1533.simplify);
            erase_universes = (uu___107_1533.erase_universes);
            allow_unbound_universes = (uu___107_1533.allow_unbound_universes);
            reify_ = (uu___107_1533.reify_);
            compress_uvars = (uu___107_1533.compress_uvars);
            no_full_norm = (uu___107_1533.no_full_norm);
            check_no_uvars = (uu___107_1533.check_no_uvars);
            unmeta = (uu___107_1533.unmeta);
            unascribe = (uu___107_1533.unascribe);
            in_full_norm_request = (uu___107_1533.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___107_1533.weakly_reduce_scrutinee)
          }
      | UnfoldUntil d ->
          let uu___108_1535 = fs  in
          {
            beta = (uu___108_1535.beta);
            iota = (uu___108_1535.iota);
            zeta = (uu___108_1535.zeta);
            weak = (uu___108_1535.weak);
            hnf = (uu___108_1535.hnf);
            primops = (uu___108_1535.primops);
            do_not_unfold_pure_lets = (uu___108_1535.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___108_1535.unfold_only);
            unfold_fully = (uu___108_1535.unfold_fully);
            unfold_attr = (uu___108_1535.unfold_attr);
            unfold_tac = (uu___108_1535.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1535.pure_subterms_within_computations);
            simplify = (uu___108_1535.simplify);
            erase_universes = (uu___108_1535.erase_universes);
            allow_unbound_universes = (uu___108_1535.allow_unbound_universes);
            reify_ = (uu___108_1535.reify_);
            compress_uvars = (uu___108_1535.compress_uvars);
            no_full_norm = (uu___108_1535.no_full_norm);
            check_no_uvars = (uu___108_1535.check_no_uvars);
            unmeta = (uu___108_1535.unmeta);
            unascribe = (uu___108_1535.unascribe);
            in_full_norm_request = (uu___108_1535.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___108_1535.weakly_reduce_scrutinee)
          }
      | UnfoldOnly lids ->
          let uu___109_1539 = fs  in
          {
            beta = (uu___109_1539.beta);
            iota = (uu___109_1539.iota);
            zeta = (uu___109_1539.zeta);
            weak = (uu___109_1539.weak);
            hnf = (uu___109_1539.hnf);
            primops = (uu___109_1539.primops);
            do_not_unfold_pure_lets = (uu___109_1539.do_not_unfold_pure_lets);
            unfold_until = (uu___109_1539.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___109_1539.unfold_fully);
            unfold_attr = (uu___109_1539.unfold_attr);
            unfold_tac = (uu___109_1539.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1539.pure_subterms_within_computations);
            simplify = (uu___109_1539.simplify);
            erase_universes = (uu___109_1539.erase_universes);
            allow_unbound_universes = (uu___109_1539.allow_unbound_universes);
            reify_ = (uu___109_1539.reify_);
            compress_uvars = (uu___109_1539.compress_uvars);
            no_full_norm = (uu___109_1539.no_full_norm);
            check_no_uvars = (uu___109_1539.check_no_uvars);
            unmeta = (uu___109_1539.unmeta);
            unascribe = (uu___109_1539.unascribe);
            in_full_norm_request = (uu___109_1539.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___109_1539.weakly_reduce_scrutinee)
          }
      | UnfoldFully lids ->
          let uu___110_1545 = fs  in
          {
            beta = (uu___110_1545.beta);
            iota = (uu___110_1545.iota);
            zeta = (uu___110_1545.zeta);
            weak = (uu___110_1545.weak);
            hnf = (uu___110_1545.hnf);
            primops = (uu___110_1545.primops);
            do_not_unfold_pure_lets = (uu___110_1545.do_not_unfold_pure_lets);
            unfold_until = (uu___110_1545.unfold_until);
            unfold_only = (uu___110_1545.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___110_1545.unfold_attr);
            unfold_tac = (uu___110_1545.unfold_tac);
            pure_subterms_within_computations =
              (uu___110_1545.pure_subterms_within_computations);
            simplify = (uu___110_1545.simplify);
            erase_universes = (uu___110_1545.erase_universes);
            allow_unbound_universes = (uu___110_1545.allow_unbound_universes);
            reify_ = (uu___110_1545.reify_);
            compress_uvars = (uu___110_1545.compress_uvars);
            no_full_norm = (uu___110_1545.no_full_norm);
            check_no_uvars = (uu___110_1545.check_no_uvars);
            unmeta = (uu___110_1545.unmeta);
            unascribe = (uu___110_1545.unascribe);
            in_full_norm_request = (uu___110_1545.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___110_1545.weakly_reduce_scrutinee)
          }
      | UnfoldAttr attr ->
          let uu___111_1549 = fs  in
          {
            beta = (uu___111_1549.beta);
            iota = (uu___111_1549.iota);
            zeta = (uu___111_1549.zeta);
            weak = (uu___111_1549.weak);
            hnf = (uu___111_1549.hnf);
            primops = (uu___111_1549.primops);
            do_not_unfold_pure_lets = (uu___111_1549.do_not_unfold_pure_lets);
            unfold_until = (uu___111_1549.unfold_until);
            unfold_only = (uu___111_1549.unfold_only);
            unfold_fully = (uu___111_1549.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___111_1549.unfold_tac);
            pure_subterms_within_computations =
              (uu___111_1549.pure_subterms_within_computations);
            simplify = (uu___111_1549.simplify);
            erase_universes = (uu___111_1549.erase_universes);
            allow_unbound_universes = (uu___111_1549.allow_unbound_universes);
            reify_ = (uu___111_1549.reify_);
            compress_uvars = (uu___111_1549.compress_uvars);
            no_full_norm = (uu___111_1549.no_full_norm);
            check_no_uvars = (uu___111_1549.check_no_uvars);
            unmeta = (uu___111_1549.unmeta);
            unascribe = (uu___111_1549.unascribe);
            in_full_norm_request = (uu___111_1549.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___111_1549.weakly_reduce_scrutinee)
          }
      | UnfoldTac  ->
          let uu___112_1550 = fs  in
          {
            beta = (uu___112_1550.beta);
            iota = (uu___112_1550.iota);
            zeta = (uu___112_1550.zeta);
            weak = (uu___112_1550.weak);
            hnf = (uu___112_1550.hnf);
            primops = (uu___112_1550.primops);
            do_not_unfold_pure_lets = (uu___112_1550.do_not_unfold_pure_lets);
            unfold_until = (uu___112_1550.unfold_until);
            unfold_only = (uu___112_1550.unfold_only);
            unfold_fully = (uu___112_1550.unfold_fully);
            unfold_attr = (uu___112_1550.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___112_1550.pure_subterms_within_computations);
            simplify = (uu___112_1550.simplify);
            erase_universes = (uu___112_1550.erase_universes);
            allow_unbound_universes = (uu___112_1550.allow_unbound_universes);
            reify_ = (uu___112_1550.reify_);
            compress_uvars = (uu___112_1550.compress_uvars);
            no_full_norm = (uu___112_1550.no_full_norm);
            check_no_uvars = (uu___112_1550.check_no_uvars);
            unmeta = (uu___112_1550.unmeta);
            unascribe = (uu___112_1550.unascribe);
            in_full_norm_request = (uu___112_1550.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___112_1550.weakly_reduce_scrutinee)
          }
      | PureSubtermsWithinComputations  ->
          let uu___113_1551 = fs  in
          {
            beta = (uu___113_1551.beta);
            iota = (uu___113_1551.iota);
            zeta = (uu___113_1551.zeta);
            weak = (uu___113_1551.weak);
            hnf = (uu___113_1551.hnf);
            primops = (uu___113_1551.primops);
            do_not_unfold_pure_lets = (uu___113_1551.do_not_unfold_pure_lets);
            unfold_until = (uu___113_1551.unfold_until);
            unfold_only = (uu___113_1551.unfold_only);
            unfold_fully = (uu___113_1551.unfold_fully);
            unfold_attr = (uu___113_1551.unfold_attr);
            unfold_tac = (uu___113_1551.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___113_1551.simplify);
            erase_universes = (uu___113_1551.erase_universes);
            allow_unbound_universes = (uu___113_1551.allow_unbound_universes);
            reify_ = (uu___113_1551.reify_);
            compress_uvars = (uu___113_1551.compress_uvars);
            no_full_norm = (uu___113_1551.no_full_norm);
            check_no_uvars = (uu___113_1551.check_no_uvars);
            unmeta = (uu___113_1551.unmeta);
            unascribe = (uu___113_1551.unascribe);
            in_full_norm_request = (uu___113_1551.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___113_1551.weakly_reduce_scrutinee)
          }
      | Simplify  ->
          let uu___114_1552 = fs  in
          {
            beta = (uu___114_1552.beta);
            iota = (uu___114_1552.iota);
            zeta = (uu___114_1552.zeta);
            weak = (uu___114_1552.weak);
            hnf = (uu___114_1552.hnf);
            primops = (uu___114_1552.primops);
            do_not_unfold_pure_lets = (uu___114_1552.do_not_unfold_pure_lets);
            unfold_until = (uu___114_1552.unfold_until);
            unfold_only = (uu___114_1552.unfold_only);
            unfold_fully = (uu___114_1552.unfold_fully);
            unfold_attr = (uu___114_1552.unfold_attr);
            unfold_tac = (uu___114_1552.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1552.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___114_1552.erase_universes);
            allow_unbound_universes = (uu___114_1552.allow_unbound_universes);
            reify_ = (uu___114_1552.reify_);
            compress_uvars = (uu___114_1552.compress_uvars);
            no_full_norm = (uu___114_1552.no_full_norm);
            check_no_uvars = (uu___114_1552.check_no_uvars);
            unmeta = (uu___114_1552.unmeta);
            unascribe = (uu___114_1552.unascribe);
            in_full_norm_request = (uu___114_1552.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___114_1552.weakly_reduce_scrutinee)
          }
      | EraseUniverses  ->
          let uu___115_1553 = fs  in
          {
            beta = (uu___115_1553.beta);
            iota = (uu___115_1553.iota);
            zeta = (uu___115_1553.zeta);
            weak = (uu___115_1553.weak);
            hnf = (uu___115_1553.hnf);
            primops = (uu___115_1553.primops);
            do_not_unfold_pure_lets = (uu___115_1553.do_not_unfold_pure_lets);
            unfold_until = (uu___115_1553.unfold_until);
            unfold_only = (uu___115_1553.unfold_only);
            unfold_fully = (uu___115_1553.unfold_fully);
            unfold_attr = (uu___115_1553.unfold_attr);
            unfold_tac = (uu___115_1553.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1553.pure_subterms_within_computations);
            simplify = (uu___115_1553.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___115_1553.allow_unbound_universes);
            reify_ = (uu___115_1553.reify_);
            compress_uvars = (uu___115_1553.compress_uvars);
            no_full_norm = (uu___115_1553.no_full_norm);
            check_no_uvars = (uu___115_1553.check_no_uvars);
            unmeta = (uu___115_1553.unmeta);
            unascribe = (uu___115_1553.unascribe);
            in_full_norm_request = (uu___115_1553.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___115_1553.weakly_reduce_scrutinee)
          }
      | AllowUnboundUniverses  ->
          let uu___116_1554 = fs  in
          {
            beta = (uu___116_1554.beta);
            iota = (uu___116_1554.iota);
            zeta = (uu___116_1554.zeta);
            weak = (uu___116_1554.weak);
            hnf = (uu___116_1554.hnf);
            primops = (uu___116_1554.primops);
            do_not_unfold_pure_lets = (uu___116_1554.do_not_unfold_pure_lets);
            unfold_until = (uu___116_1554.unfold_until);
            unfold_only = (uu___116_1554.unfold_only);
            unfold_fully = (uu___116_1554.unfold_fully);
            unfold_attr = (uu___116_1554.unfold_attr);
            unfold_tac = (uu___116_1554.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1554.pure_subterms_within_computations);
            simplify = (uu___116_1554.simplify);
            erase_universes = (uu___116_1554.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___116_1554.reify_);
            compress_uvars = (uu___116_1554.compress_uvars);
            no_full_norm = (uu___116_1554.no_full_norm);
            check_no_uvars = (uu___116_1554.check_no_uvars);
            unmeta = (uu___116_1554.unmeta);
            unascribe = (uu___116_1554.unascribe);
            in_full_norm_request = (uu___116_1554.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___116_1554.weakly_reduce_scrutinee)
          }
      | Reify  ->
          let uu___117_1555 = fs  in
          {
            beta = (uu___117_1555.beta);
            iota = (uu___117_1555.iota);
            zeta = (uu___117_1555.zeta);
            weak = (uu___117_1555.weak);
            hnf = (uu___117_1555.hnf);
            primops = (uu___117_1555.primops);
            do_not_unfold_pure_lets = (uu___117_1555.do_not_unfold_pure_lets);
            unfold_until = (uu___117_1555.unfold_until);
            unfold_only = (uu___117_1555.unfold_only);
            unfold_fully = (uu___117_1555.unfold_fully);
            unfold_attr = (uu___117_1555.unfold_attr);
            unfold_tac = (uu___117_1555.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1555.pure_subterms_within_computations);
            simplify = (uu___117_1555.simplify);
            erase_universes = (uu___117_1555.erase_universes);
            allow_unbound_universes = (uu___117_1555.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___117_1555.compress_uvars);
            no_full_norm = (uu___117_1555.no_full_norm);
            check_no_uvars = (uu___117_1555.check_no_uvars);
            unmeta = (uu___117_1555.unmeta);
            unascribe = (uu___117_1555.unascribe);
            in_full_norm_request = (uu___117_1555.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___117_1555.weakly_reduce_scrutinee)
          }
      | CompressUvars  ->
          let uu___118_1556 = fs  in
          {
            beta = (uu___118_1556.beta);
            iota = (uu___118_1556.iota);
            zeta = (uu___118_1556.zeta);
            weak = (uu___118_1556.weak);
            hnf = (uu___118_1556.hnf);
            primops = (uu___118_1556.primops);
            do_not_unfold_pure_lets = (uu___118_1556.do_not_unfold_pure_lets);
            unfold_until = (uu___118_1556.unfold_until);
            unfold_only = (uu___118_1556.unfold_only);
            unfold_fully = (uu___118_1556.unfold_fully);
            unfold_attr = (uu___118_1556.unfold_attr);
            unfold_tac = (uu___118_1556.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1556.pure_subterms_within_computations);
            simplify = (uu___118_1556.simplify);
            erase_universes = (uu___118_1556.erase_universes);
            allow_unbound_universes = (uu___118_1556.allow_unbound_universes);
            reify_ = (uu___118_1556.reify_);
            compress_uvars = true;
            no_full_norm = (uu___118_1556.no_full_norm);
            check_no_uvars = (uu___118_1556.check_no_uvars);
            unmeta = (uu___118_1556.unmeta);
            unascribe = (uu___118_1556.unascribe);
            in_full_norm_request = (uu___118_1556.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___118_1556.weakly_reduce_scrutinee)
          }
      | NoFullNorm  ->
          let uu___119_1557 = fs  in
          {
            beta = (uu___119_1557.beta);
            iota = (uu___119_1557.iota);
            zeta = (uu___119_1557.zeta);
            weak = (uu___119_1557.weak);
            hnf = (uu___119_1557.hnf);
            primops = (uu___119_1557.primops);
            do_not_unfold_pure_lets = (uu___119_1557.do_not_unfold_pure_lets);
            unfold_until = (uu___119_1557.unfold_until);
            unfold_only = (uu___119_1557.unfold_only);
            unfold_fully = (uu___119_1557.unfold_fully);
            unfold_attr = (uu___119_1557.unfold_attr);
            unfold_tac = (uu___119_1557.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1557.pure_subterms_within_computations);
            simplify = (uu___119_1557.simplify);
            erase_universes = (uu___119_1557.erase_universes);
            allow_unbound_universes = (uu___119_1557.allow_unbound_universes);
            reify_ = (uu___119_1557.reify_);
            compress_uvars = (uu___119_1557.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___119_1557.check_no_uvars);
            unmeta = (uu___119_1557.unmeta);
            unascribe = (uu___119_1557.unascribe);
            in_full_norm_request = (uu___119_1557.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___119_1557.weakly_reduce_scrutinee)
          }
      | CheckNoUvars  ->
          let uu___120_1558 = fs  in
          {
            beta = (uu___120_1558.beta);
            iota = (uu___120_1558.iota);
            zeta = (uu___120_1558.zeta);
            weak = (uu___120_1558.weak);
            hnf = (uu___120_1558.hnf);
            primops = (uu___120_1558.primops);
            do_not_unfold_pure_lets = (uu___120_1558.do_not_unfold_pure_lets);
            unfold_until = (uu___120_1558.unfold_until);
            unfold_only = (uu___120_1558.unfold_only);
            unfold_fully = (uu___120_1558.unfold_fully);
            unfold_attr = (uu___120_1558.unfold_attr);
            unfold_tac = (uu___120_1558.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_1558.pure_subterms_within_computations);
            simplify = (uu___120_1558.simplify);
            erase_universes = (uu___120_1558.erase_universes);
            allow_unbound_universes = (uu___120_1558.allow_unbound_universes);
            reify_ = (uu___120_1558.reify_);
            compress_uvars = (uu___120_1558.compress_uvars);
            no_full_norm = (uu___120_1558.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___120_1558.unmeta);
            unascribe = (uu___120_1558.unascribe);
            in_full_norm_request = (uu___120_1558.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___120_1558.weakly_reduce_scrutinee)
          }
      | Unmeta  ->
          let uu___121_1559 = fs  in
          {
            beta = (uu___121_1559.beta);
            iota = (uu___121_1559.iota);
            zeta = (uu___121_1559.zeta);
            weak = (uu___121_1559.weak);
            hnf = (uu___121_1559.hnf);
            primops = (uu___121_1559.primops);
            do_not_unfold_pure_lets = (uu___121_1559.do_not_unfold_pure_lets);
            unfold_until = (uu___121_1559.unfold_until);
            unfold_only = (uu___121_1559.unfold_only);
            unfold_fully = (uu___121_1559.unfold_fully);
            unfold_attr = (uu___121_1559.unfold_attr);
            unfold_tac = (uu___121_1559.unfold_tac);
            pure_subterms_within_computations =
              (uu___121_1559.pure_subterms_within_computations);
            simplify = (uu___121_1559.simplify);
            erase_universes = (uu___121_1559.erase_universes);
            allow_unbound_universes = (uu___121_1559.allow_unbound_universes);
            reify_ = (uu___121_1559.reify_);
            compress_uvars = (uu___121_1559.compress_uvars);
            no_full_norm = (uu___121_1559.no_full_norm);
            check_no_uvars = (uu___121_1559.check_no_uvars);
            unmeta = true;
            unascribe = (uu___121_1559.unascribe);
            in_full_norm_request = (uu___121_1559.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___121_1559.weakly_reduce_scrutinee)
          }
      | Unascribe  ->
          let uu___122_1560 = fs  in
          {
            beta = (uu___122_1560.beta);
            iota = (uu___122_1560.iota);
            zeta = (uu___122_1560.zeta);
            weak = (uu___122_1560.weak);
            hnf = (uu___122_1560.hnf);
            primops = (uu___122_1560.primops);
            do_not_unfold_pure_lets = (uu___122_1560.do_not_unfold_pure_lets);
            unfold_until = (uu___122_1560.unfold_until);
            unfold_only = (uu___122_1560.unfold_only);
            unfold_fully = (uu___122_1560.unfold_fully);
            unfold_attr = (uu___122_1560.unfold_attr);
            unfold_tac = (uu___122_1560.unfold_tac);
            pure_subterms_within_computations =
              (uu___122_1560.pure_subterms_within_computations);
            simplify = (uu___122_1560.simplify);
            erase_universes = (uu___122_1560.erase_universes);
            allow_unbound_universes = (uu___122_1560.allow_unbound_universes);
            reify_ = (uu___122_1560.reify_);
            compress_uvars = (uu___122_1560.compress_uvars);
            no_full_norm = (uu___122_1560.no_full_norm);
            check_no_uvars = (uu___122_1560.check_no_uvars);
            unmeta = (uu___122_1560.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___122_1560.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___122_1560.weakly_reduce_scrutinee)
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
  norm_delayed: Prims.bool ;
  print_normalized: Prims.bool }[@@deriving show]
let (__proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__gen
  
let (__proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__primop
  
let (__proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__b380
  
let (__proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__norm_delayed
  
let (__proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
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
             let uu____2330 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2330 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2344 = FStar_Util.psmap_empty ()  in add_steps uu____2344 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2359 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2359
  
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
    match projectee with | Arg _0 -> true | uu____2517 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2555 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2593 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2666 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2716 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2774 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2818 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2858 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2896 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2914 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2941 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2941 with | (hd1,uu____2955) -> hd1
  
let mk :
  'Auu____2978 .
    'Auu____2978 ->
      FStar_Range.range -> 'Auu____2978 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____3041 = FStar_ST.op_Bang r  in
          match uu____3041 with
          | FStar_Pervasives_Native.Some uu____3093 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____3169 =
      FStar_List.map
        (fun uu____3183  ->
           match uu____3183 with
           | (bopt,c) ->
               let uu____3196 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____3198 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____3196 uu____3198) env
       in
    FStar_All.pipe_right uu____3169 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___81_3201  ->
    match uu___81_3201 with
    | Clos (env,t,uu____3204,uu____3205) ->
        let uu____3250 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____3257 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____3250 uu____3257
    | Univ uu____3258 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___82_3263  ->
    match uu___82_3263 with
    | Arg (c,uu____3265,uu____3266) ->
        let uu____3267 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____3267
    | MemoLazy uu____3268 -> "MemoLazy"
    | Abs (uu____3275,bs,uu____3277,uu____3278,uu____3279) ->
        let uu____3284 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____3284
    | UnivArgs uu____3289 -> "UnivArgs"
    | Match uu____3296 -> "Match"
    | App (uu____3305,t,uu____3307,uu____3308) ->
        let uu____3309 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____3309
    | Meta (uu____3310,m,uu____3312) -> "Meta"
    | Let uu____3313 -> "Let"
    | Cfg uu____3322 -> "Cfg"
    | Debug (t,uu____3324) ->
        let uu____3325 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____3325
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____3335 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3335 (FStar_String.concat "; ")
  
let (log : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (unit -> unit) -> unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____3376 . 'Auu____3376 Prims.list -> Prims.bool =
  fun uu___83_3383  ->
    match uu___83_3383 with | [] -> true | uu____3386 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____3418 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____3418
      with
      | uu____3437 ->
          let uu____3438 =
            let uu____3439 = FStar_Syntax_Print.db_to_string x  in
            let uu____3440 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3439
              uu____3440
             in
          failwith uu____3438
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____3448 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____3448
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____3452 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____3452
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____3456 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____3456
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
          let uu____3490 =
            FStar_List.fold_left
              (fun uu____3516  ->
                 fun u1  ->
                   match uu____3516 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____3541 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____3541 with
                        | (k_u,n1) ->
                            let uu____3556 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3556
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____3490 with
          | (uu____3574,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3601 =
                   let uu____3602 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3602  in
                 match uu____3601 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3620 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3628 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3634 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3643 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3652 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3659 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3659 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3676 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3676 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3684 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3692 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3692 with
                                  | (uu____3697,m) -> n1 <= m))
                           in
                        if uu____3684 then rest1 else us1
                    | uu____3702 -> us1)
               | uu____3707 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3711 = aux u3  in
              FStar_List.map (fun _0_17  -> FStar_Syntax_Syntax.U_succ _0_17)
                uu____3711
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3715 = aux u  in
           match uu____3715 with
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
            (fun uu____3863  ->
               let uu____3864 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3865 = env_to_string env  in
               let uu____3866 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3864 uu____3865 uu____3866);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3875 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3878 ->
                    let uu____3903 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3903
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3904 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3905 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3906 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3907 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar uu____3908 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3914 ->
                           let uu____3915 =
                             let uu____3916 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____3917 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____3916 uu____3917
                              in
                           failwith uu____3915
                       | uu____3920 -> inline_closure_env cfg env stack t1)
                    else rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____3926 =
                        let uu____3927 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____3927  in
                      mk uu____3926 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____3935 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3935  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____3937 = lookup_bvar env x  in
                    (match uu____3937 with
                     | Univ uu____3940 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___127_3944 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___127_3944.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___127_3944.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____3950,uu____3951) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4036  ->
                              fun stack1  ->
                                match uu____4036 with
                                | (a,aq) ->
                                    let uu____4048 =
                                      let uu____4049 =
                                        let uu____4056 =
                                          let uu____4057 =
                                            let uu____4088 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4088, false)  in
                                          Clos uu____4057  in
                                        (uu____4056, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4049  in
                                    uu____4048 :: stack1) args)
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
                    let uu____4264 = close_binders cfg env bs  in
                    (match uu____4264 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4311 =
                      let uu____4322 =
                        let uu____4329 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4329]  in
                      close_binders cfg env uu____4322  in
                    (match uu____4311 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4352 =
                             let uu____4353 =
                               let uu____4360 =
                                 let uu____4361 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4361
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4360, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4353  in
                           mk uu____4352 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4452 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4452
                      | FStar_Util.Inr c ->
                          let uu____4466 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4466
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4485 =
                        let uu____4486 =
                          let uu____4513 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4513, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4486  in
                      mk uu____4485 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4559 =
                            let uu____4560 =
                              let uu____4567 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4567, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4560  in
                          mk uu____4559 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4619  -> dummy :: env1) env
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
                    let uu____4640 =
                      let uu____4651 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4651
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4670 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___128_4686 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___128_4686.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___128_4686.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4670))
                       in
                    (match uu____4640 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___129_4704 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___129_4704.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___129_4704.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___129_4704.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___129_4704.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4718,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4781  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4798 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4798
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4810  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4834 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4834
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___130_4842 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___130_4842.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___130_4842.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___131_4843 = lb  in
                      let uu____4844 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___131_4843.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___131_4843.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4844;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___131_4843.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___131_4843.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____4876  -> fun env1  -> dummy :: env1)
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
            (fun uu____4965  ->
               let uu____4966 = FStar_Syntax_Print.tag_of_term t  in
               let uu____4967 = env_to_string env  in
               let uu____4968 = stack_to_string stack  in
               let uu____4969 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____4966 uu____4967 uu____4968 uu____4969);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____4974,uu____4975),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5052 = close_binders cfg env' bs  in
               (match uu____5052 with
                | (bs1,uu____5066) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5082 =
                      let uu___132_5085 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___132_5085.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___132_5085.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5082)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5141 =
                 match uu____5141 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5256 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5285 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5369  ->
                                     fun uu____5370  ->
                                       match (uu____5369, uu____5370) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5509 = norm_pat env4 p1
                                              in
                                           (match uu____5509 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5285 with
                            | (pats1,env4) ->
                                ((let uu___133_5671 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___133_5671.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___134_5690 = x  in
                             let uu____5691 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___134_5690.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___134_5690.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5691
                             }  in
                           ((let uu___135_5705 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___135_5705.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___136_5716 = x  in
                             let uu____5717 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___136_5716.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___136_5716.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5717
                             }  in
                           ((let uu___137_5731 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___137_5731.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___138_5747 = x  in
                             let uu____5748 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___138_5747.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___138_5747.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5748
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___139_5765 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___139_5765.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5770 = norm_pat env2 pat  in
                     (match uu____5770 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____5839 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____5839
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____5858 =
                   let uu____5859 =
                     let uu____5882 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____5882)  in
                   FStar_Syntax_Syntax.Tm_match uu____5859  in
                 mk uu____5858 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____5995 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____6084  ->
                                       match uu____6084 with
                                       | (a,q) ->
                                           let uu____6103 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____6103, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____5995
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____6114 =
                       let uu____6121 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____6121)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____6114
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____6133 =
                       let uu____6142 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____6142)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____6133
                 | uu____6147 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____6153 -> failwith "Impossible: unexpected stack element")

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
        let uu____6167 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6240  ->
                  fun uu____6241  ->
                    match (uu____6240, uu____6241) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___140_6359 = b  in
                          let uu____6360 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___140_6359.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___140_6359.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6360
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6167 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6477 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6490 = inline_closure_env cfg env [] t  in
                 let uu____6491 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6490 uu____6491
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6504 = inline_closure_env cfg env [] t  in
                 let uu____6505 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6504 uu____6505
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6549  ->
                           match uu____6549 with
                           | (a,q) ->
                               let uu____6562 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6562, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___84_6577  ->
                           match uu___84_6577 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6581 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6581
                           | f -> f))
                    in
                 let uu____6585 =
                   let uu___141_6586 = c1  in
                   let uu____6587 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6587;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___141_6586.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6585)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___85_6597  ->
            match uu___85_6597 with
            | FStar_Syntax_Syntax.DECREASES uu____6598 -> false
            | uu____6601 -> true))

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
                   (fun uu___86_6619  ->
                      match uu___86_6619 with
                      | FStar_Syntax_Syntax.DECREASES uu____6620 -> false
                      | uu____6623 -> true))
               in
            let rc1 =
              let uu___142_6625 = rc  in
              let uu____6626 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___142_6625.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6626;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6635 -> lopt

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
    let uu____6740 =
      let uu____6749 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6749  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6740  in
  let arg_as_bounded_int uu____6775 =
    match uu____6775 with
    | (a,uu____6787) ->
        let uu____6794 =
          let uu____6795 = FStar_Syntax_Subst.compress a  in
          uu____6795.FStar_Syntax_Syntax.n  in
        (match uu____6794 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6805;
                FStar_Syntax_Syntax.vars = uu____6806;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6808;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6809;_},uu____6810)::[])
             when
             let uu____6849 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6849 "int_to_t" ->
             let uu____6850 =
               let uu____6855 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6855)  in
             FStar_Pervasives_Native.Some uu____6850
         | uu____6860 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6908 = f a  in FStar_Pervasives_Native.Some uu____6908
    | uu____6909 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____6965 = f a0 a1  in FStar_Pervasives_Native.Some uu____6965
    | uu____6966 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____7024 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____7024  in
  let binary_op as_a f res args =
    let uu____7095 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____7095  in
  let as_primitive_step is_strong uu____7132 =
    match uu____7132 with
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
           let uu____7192 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____7192)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7228 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____7228)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____7257 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____7257)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7293 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7293)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7329 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7329)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7461 =
          let uu____7470 = as_a a  in
          let uu____7473 = as_b b  in (uu____7470, uu____7473)  in
        (match uu____7461 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7488 =
               let uu____7489 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7489  in
             FStar_Pervasives_Native.Some uu____7488
         | uu____7490 -> FStar_Pervasives_Native.None)
    | uu____7499 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7519 =
        let uu____7520 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7520  in
      mk uu____7519 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7532 =
      let uu____7535 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7535  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7532  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7577 =
      let uu____7578 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7578  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7577
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7642 = arg_as_string a1  in
        (match uu____7642 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7648 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7648 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7661 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7661
              | uu____7662 -> FStar_Pervasives_Native.None)
         | uu____7667 -> FStar_Pervasives_Native.None)
    | uu____7670 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7690 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7690
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7727 =
          let uu____7748 = arg_as_string fn  in
          let uu____7751 = arg_as_int from_line  in
          let uu____7754 = arg_as_int from_col  in
          let uu____7757 = arg_as_int to_line  in
          let uu____7760 = arg_as_int to_col  in
          (uu____7748, uu____7751, uu____7754, uu____7757, uu____7760)  in
        (match uu____7727 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7791 =
                 let uu____7792 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7793 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7792 uu____7793  in
               let uu____7794 =
                 let uu____7795 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7796 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7795 uu____7796  in
               FStar_Range.mk_range fn1 uu____7791 uu____7794  in
             let uu____7797 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7797
         | uu____7798 -> FStar_Pervasives_Native.None)
    | uu____7819 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____7852)::(a1,uu____7854)::(a2,uu____7856)::[] ->
        let uu____7893 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7893 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____7898 -> FStar_Pervasives_Native.None)
    | uu____7899 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____7930)::[] ->
        let uu____7939 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____7939 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7945 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7945
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7946 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____7972 =
      let uu____7989 =
        let uu____8006 =
          let uu____8023 =
            let uu____8040 =
              let uu____8057 =
                let uu____8074 =
                  let uu____8091 =
                    let uu____8108 =
                      let uu____8125 =
                        let uu____8142 =
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
                                                let uu____8344 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8344,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8353 =
                                                let uu____8370 =
                                                  let uu____8385 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8385,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8398 =
                                                  let uu____8415 =
                                                    let uu____8430 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8430,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8439 =
                                                    let uu____8456 =
                                                      let uu____8471 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8471,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8456]  in
                                                  uu____8415 :: uu____8439
                                                   in
                                                uu____8370 :: uu____8398  in
                                              uu____8329 :: uu____8353  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8312
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8295
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8278
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8261
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8244
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8691 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8691 y)))
                                    :: uu____8227
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____8210
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____8193
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____8176
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____8159
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____8142
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8125
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____8886 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____8886)))
                      :: uu____8108
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____8916 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____8916)))
                    :: uu____8091
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____8946 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____8946)))
                  :: uu____8074
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____8976 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____8976)))
                :: uu____8057
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8040
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8023
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8006
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____7989
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____7972
     in
  let weak_ops =
    let uu____9131 =
      let uu____9146 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____9146, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____9131]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9226 =
        let uu____9231 =
          let uu____9232 = FStar_Syntax_Syntax.as_arg c  in [uu____9232]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9231  in
      uu____9226 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9306 =
                let uu____9321 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9321, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9343  ->
                          fun uu____9344  ->
                            match (uu____9343, uu____9344) with
                            | ((int_to_t1,x),(uu____9363,y)) ->
                                let uu____9373 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9373)))
                 in
              let uu____9374 =
                let uu____9391 =
                  let uu____9406 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9406, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9428  ->
                            fun uu____9429  ->
                              match (uu____9428, uu____9429) with
                              | ((int_to_t1,x),(uu____9448,y)) ->
                                  let uu____9458 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9458)))
                   in
                let uu____9459 =
                  let uu____9476 =
                    let uu____9491 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9491, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9513  ->
                              fun uu____9514  ->
                                match (uu____9513, uu____9514) with
                                | ((int_to_t1,x),(uu____9533,y)) ->
                                    let uu____9543 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9543)))
                     in
                  let uu____9544 =
                    let uu____9561 =
                      let uu____9576 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9576, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9594  ->
                                match uu____9594 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9561]  in
                  uu____9476 :: uu____9544  in
                uu____9391 :: uu____9459  in
              uu____9306 :: uu____9374))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9724 =
                let uu____9739 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9739, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9761  ->
                          fun uu____9762  ->
                            match (uu____9761, uu____9762) with
                            | ((int_to_t1,x),(uu____9781,y)) ->
                                let uu____9791 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9791)))
                 in
              let uu____9792 =
                let uu____9809 =
                  let uu____9824 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9824, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9846  ->
                            fun uu____9847  ->
                              match (uu____9846, uu____9847) with
                              | ((int_to_t1,x),(uu____9866,y)) ->
                                  let uu____9876 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9876)))
                   in
                [uu____9809]  in
              uu____9724 :: uu____9792))
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
    | (_typ,uu____10006)::(a1,uu____10008)::(a2,uu____10010)::[] ->
        let uu____10047 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10047 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___143_10051 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___143_10051.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___143_10051.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___144_10053 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___144_10053.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___144_10053.FStar_Syntax_Syntax.vars)
                })
         | uu____10054 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10056)::uu____10057::(a1,uu____10059)::(a2,uu____10061)::[]
        ->
        let uu____10110 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10110 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___143_10114 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___143_10114.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___143_10114.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___144_10116 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___144_10116.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___144_10116.FStar_Syntax_Syntax.vars)
                })
         | uu____10117 -> FStar_Pervasives_Native.None)
    | uu____10118 -> failwith "Unexpected number of arguments"  in
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
    let uu____10172 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____10172 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____10224 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10224) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10286  ->
           fun subst1  ->
             match uu____10286 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10327,uu____10328)) ->
                      let uu____10387 = b  in
                      (match uu____10387 with
                       | (bv,uu____10395) ->
                           let uu____10396 =
                             let uu____10397 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10397  in
                           if uu____10396
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10402 = unembed_binder term1  in
                              match uu____10402 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10409 =
                                      let uu___145_10410 = bv  in
                                      let uu____10411 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___145_10410.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___145_10410.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10411
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10409
                                     in
                                  let b_for_x =
                                    let uu____10415 =
                                      let uu____10422 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10422)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10415  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___87_10436  ->
                                         match uu___87_10436 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10437,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10439;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10440;_})
                                             ->
                                             let uu____10445 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10445
                                         | uu____10446 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10447 -> subst1)) env []
  
let reduce_primops :
  'Auu____10470 'Auu____10471 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10470) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10471 ->
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
            (let uu____10519 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10519 with
             | (head1,args) ->
                 let uu____10552 =
                   let uu____10553 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10553.FStar_Syntax_Syntax.n  in
                 (match uu____10552 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10559 = find_prim_step cfg fv  in
                      (match uu____10559 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10585  ->
                                   let uu____10586 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10587 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10594 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10586 uu____10587 uu____10594);
                              tm)
                           else
                             (let uu____10596 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10596 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10709  ->
                                        let uu____10710 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10710);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10713  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10715 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10715 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10723  ->
                                              let uu____10724 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10724);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10730  ->
                                              let uu____10731 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10732 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10731 uu____10732);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10733 ->
                           (log_primops cfg
                              (fun uu____10737  ->
                                 let uu____10738 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10738);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10742  ->
                            let uu____10743 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10743);
                       (match args with
                        | (a1,uu____10747)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10764 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10776  ->
                            let uu____10777 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10777);
                       (match args with
                        | (t,uu____10781)::(r,uu____10783)::[] ->
                            let uu____10810 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____10810 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___146_10816 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___146_10816.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___146_10816.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____10819 -> tm))
                  | uu____10828 -> tm))
  
let reduce_equality :
  'Auu____10839 'Auu____10840 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10839) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10840 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___147_10886 = cfg  in
         {
           steps =
             (let uu___148_10889 = default_steps  in
              {
                beta = (uu___148_10889.beta);
                iota = (uu___148_10889.iota);
                zeta = (uu___148_10889.zeta);
                weak = (uu___148_10889.weak);
                hnf = (uu___148_10889.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___148_10889.do_not_unfold_pure_lets);
                unfold_until = (uu___148_10889.unfold_until);
                unfold_only = (uu___148_10889.unfold_only);
                unfold_fully = (uu___148_10889.unfold_fully);
                unfold_attr = (uu___148_10889.unfold_attr);
                unfold_tac = (uu___148_10889.unfold_tac);
                pure_subterms_within_computations =
                  (uu___148_10889.pure_subterms_within_computations);
                simplify = (uu___148_10889.simplify);
                erase_universes = (uu___148_10889.erase_universes);
                allow_unbound_universes =
                  (uu___148_10889.allow_unbound_universes);
                reify_ = (uu___148_10889.reify_);
                compress_uvars = (uu___148_10889.compress_uvars);
                no_full_norm = (uu___148_10889.no_full_norm);
                check_no_uvars = (uu___148_10889.check_no_uvars);
                unmeta = (uu___148_10889.unmeta);
                unascribe = (uu___148_10889.unascribe);
                in_full_norm_request = (uu___148_10889.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___148_10889.weakly_reduce_scrutinee)
              });
           tcenv = (uu___147_10886.tcenv);
           debug = (uu___147_10886.debug);
           delta_level = (uu___147_10886.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___147_10886.strong);
           memoize_lazy = (uu___147_10886.memoize_lazy);
           normalize_pure_lets = (uu___147_10886.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____10896 .
    FStar_Syntax_Syntax.term -> 'Auu____10896 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10911 =
        let uu____10918 =
          let uu____10919 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10919.FStar_Syntax_Syntax.n  in
        (uu____10918, args)  in
      match uu____10911 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10925::uu____10926::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10930::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10935::uu____10936::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10939 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___88_10952  ->
    match uu___88_10952 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10958 =
          let uu____10961 =
            let uu____10962 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____10962  in
          [uu____10961]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10958
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____10968 =
          let uu____10971 =
            let uu____10972 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____10972  in
          [uu____10971]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10968
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____10993 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10993) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____11039 =
          let uu____11044 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____11044 s  in
        match uu____11039 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____11060 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____11060
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____11077::(tm,uu____11079)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____11108)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____11129)::uu____11130::(tm,uu____11132)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____11173 =
            let uu____11178 = full_norm steps  in parse_steps uu____11178  in
          (match uu____11173 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____11217 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___89_11236  ->
    match uu___89_11236 with
    | (App
        (uu____11239,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11240;
                       FStar_Syntax_Syntax.vars = uu____11241;_},uu____11242,uu____11243))::uu____11244
        -> true
    | uu____11249 -> false
  
let firstn :
  'Auu____11258 .
    Prims.int ->
      'Auu____11258 Prims.list ->
        ('Auu____11258 Prims.list,'Auu____11258 Prims.list)
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
          (uu____11300,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11301;
                         FStar_Syntax_Syntax.vars = uu____11302;_},uu____11303,uu____11304))::uu____11305
          -> (cfg.steps).reify_
      | uu____11310 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11333) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11343) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11362  ->
                  match uu____11362 with
                  | (a,uu____11370) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11376 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11401 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11402 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11403 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11404 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11405 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11406 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11407 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11408 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11415 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11422 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11435 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11452 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11465 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11472 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11534  ->
                   match uu____11534 with
                   | (a,uu____11542) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11549) ->
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
                     (fun uu____11671  ->
                        match uu____11671 with
                        | (a,uu____11679) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11684,uu____11685,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11691,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11697 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11704 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11705 -> false))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____11997 ->
                   let uu____12022 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____12022
               | uu____12023 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____12031  ->
               let uu____12032 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____12033 = FStar_Syntax_Print.term_to_string t1  in
               let uu____12034 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____12041 =
                 let uu____12042 =
                   let uu____12045 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____12045
                    in
                 stack_to_string uu____12042  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____12032 uu____12033 uu____12034 uu____12041);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____12068 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____12069 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____12070 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12071;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____12072;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12075;
                 FStar_Syntax_Syntax.fv_delta = uu____12076;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12077;
                 FStar_Syntax_Syntax.fv_delta = uu____12078;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____12079);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____12086 ->
               let uu____12093 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____12093
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____12123 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____12123)
               ->
               let cfg' =
                 let uu___149_12125 = cfg  in
                 {
                   steps =
                     (let uu___150_12128 = cfg.steps  in
                      {
                        beta = (uu___150_12128.beta);
                        iota = (uu___150_12128.iota);
                        zeta = (uu___150_12128.zeta);
                        weak = (uu___150_12128.weak);
                        hnf = (uu___150_12128.hnf);
                        primops = (uu___150_12128.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___150_12128.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___150_12128.unfold_attr);
                        unfold_tac = (uu___150_12128.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___150_12128.pure_subterms_within_computations);
                        simplify = (uu___150_12128.simplify);
                        erase_universes = (uu___150_12128.erase_universes);
                        allow_unbound_universes =
                          (uu___150_12128.allow_unbound_universes);
                        reify_ = (uu___150_12128.reify_);
                        compress_uvars = (uu___150_12128.compress_uvars);
                        no_full_norm = (uu___150_12128.no_full_norm);
                        check_no_uvars = (uu___150_12128.check_no_uvars);
                        unmeta = (uu___150_12128.unmeta);
                        unascribe = (uu___150_12128.unascribe);
                        in_full_norm_request =
                          (uu___150_12128.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___150_12128.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___149_12125.tcenv);
                   debug = (uu___149_12125.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___149_12125.primitive_steps);
                   strong = (uu___149_12125.strong);
                   memoize_lazy = (uu___149_12125.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____12133 = get_norm_request (norm cfg' env []) args  in
               (match uu____12133 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____12162  ->
                              fun stack1  ->
                                match uu____12162 with
                                | (a,aq) ->
                                    let uu____12174 =
                                      let uu____12175 =
                                        let uu____12182 =
                                          let uu____12183 =
                                            let uu____12214 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____12214, false)  in
                                          Clos uu____12183  in
                                        (uu____12182, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____12175  in
                                    uu____12174 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____12302  ->
                          let uu____12303 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12303);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____12325 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___90_12330  ->
                                match uu___90_12330 with
                                | UnfoldUntil uu____12331 -> true
                                | UnfoldOnly uu____12332 -> true
                                | UnfoldFully uu____12335 -> true
                                | uu____12338 -> false))
                         in
                      if uu____12325
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___151_12343 = cfg  in
                      let uu____12344 =
                        let uu___152_12345 = to_fsteps s  in
                        {
                          beta = (uu___152_12345.beta);
                          iota = (uu___152_12345.iota);
                          zeta = (uu___152_12345.zeta);
                          weak = (uu___152_12345.weak);
                          hnf = (uu___152_12345.hnf);
                          primops = (uu___152_12345.primops);
                          do_not_unfold_pure_lets =
                            (uu___152_12345.do_not_unfold_pure_lets);
                          unfold_until = (uu___152_12345.unfold_until);
                          unfold_only = (uu___152_12345.unfold_only);
                          unfold_fully = (uu___152_12345.unfold_fully);
                          unfold_attr = (uu___152_12345.unfold_attr);
                          unfold_tac = (uu___152_12345.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___152_12345.pure_subterms_within_computations);
                          simplify = (uu___152_12345.simplify);
                          erase_universes = (uu___152_12345.erase_universes);
                          allow_unbound_universes =
                            (uu___152_12345.allow_unbound_universes);
                          reify_ = (uu___152_12345.reify_);
                          compress_uvars = (uu___152_12345.compress_uvars);
                          no_full_norm = (uu___152_12345.no_full_norm);
                          check_no_uvars = (uu___152_12345.check_no_uvars);
                          unmeta = (uu___152_12345.unmeta);
                          unascribe = (uu___152_12345.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___152_12345.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____12344;
                        tcenv = (uu___151_12343.tcenv);
                        debug = (uu___151_12343.debug);
                        delta_level;
                        primitive_steps = (uu___151_12343.primitive_steps);
                        strong = (uu___151_12343.strong);
                        memoize_lazy = (uu___151_12343.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12354 =
                          let uu____12355 =
                            let uu____12360 = FStar_Util.now ()  in
                            (t1, uu____12360)  in
                          Debug uu____12355  in
                        uu____12354 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12364 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12364
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12373 =
                      let uu____12380 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12380, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12373  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12390 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12390  in
               let uu____12391 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____12391
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____12397  ->
                       let uu____12398 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12399 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12398 uu____12399);
                  if b
                  then
                    (let uu____12400 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____12400 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____12408 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____12408) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____12421),uu____12422);
                                FStar_Syntax_Syntax.sigrng = uu____12423;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____12425;
                                FStar_Syntax_Syntax.sigattrs = uu____12426;_},uu____12427),uu____12428)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____12487 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___91_12491  ->
                               match uu___91_12491 with
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
                          (let uu____12501 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____12501))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____12520) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____12555,uu____12556) -> false)))
                     in
                  let uu____12573 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____12589 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____12589 then (true, true) else (false, false)
                     in
                  match uu____12573 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____12602  ->
                            let uu____12603 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____12604 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____12605 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____12603 uu____12604 uu____12605);
                       if should_delta2
                       then
                         (let uu____12606 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___153_12616 = cfg  in
                                 {
                                   steps =
                                     (let uu___154_12619 = cfg.steps  in
                                      {
                                        beta = (uu___154_12619.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___154_12619.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.Delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___154_12619.unfold_attr);
                                        unfold_tac =
                                          (uu___154_12619.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___154_12619.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___154_12619.erase_universes);
                                        allow_unbound_universes =
                                          (uu___154_12619.allow_unbound_universes);
                                        reify_ = (uu___154_12619.reify_);
                                        compress_uvars =
                                          (uu___154_12619.compress_uvars);
                                        no_full_norm =
                                          (uu___154_12619.no_full_norm);
                                        check_no_uvars =
                                          (uu___154_12619.check_no_uvars);
                                        unmeta = (uu___154_12619.unmeta);
                                        unascribe =
                                          (uu___154_12619.unascribe);
                                        in_full_norm_request =
                                          (uu___154_12619.in_full_norm_request);
                                        weakly_reduce_scrutinee =
                                          (uu___154_12619.weakly_reduce_scrutinee)
                                      });
                                   tcenv = (uu___153_12616.tcenv);
                                   debug = (uu___153_12616.debug);
                                   delta_level = (uu___153_12616.delta_level);
                                   primitive_steps =
                                     (uu___153_12616.primitive_steps);
                                   strong = (uu___153_12616.strong);
                                   memoize_lazy =
                                     (uu___153_12616.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___153_12616.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____12606 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12629 = lookup_bvar env x  in
               (match uu____12629 with
                | Univ uu____12630 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12679 = FStar_ST.op_Bang r  in
                      (match uu____12679 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12801  ->
                                 let uu____12802 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12803 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12802
                                   uu____12803);
                            (let uu____12804 = maybe_weakly_reduced t'  in
                             if uu____12804
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____12805 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12876)::uu____12877 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12886)::uu____12887 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12899,uu____12900))::stack_rest ->
                    (match c with
                     | Univ uu____12904 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12913 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12934  ->
                                    let uu____12935 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12935);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12963  ->
                                    let uu____12964 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12964);
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
                       (fun uu____13030  ->
                          let uu____13031 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____13031);
                     norm cfg env stack1 t1)
                | (Debug uu____13032)::uu____13033 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___155_13043 = cfg.steps  in
                             {
                               beta = (uu___155_13043.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_13043.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_13043.unfold_until);
                               unfold_only = (uu___155_13043.unfold_only);
                               unfold_fully = (uu___155_13043.unfold_fully);
                               unfold_attr = (uu___155_13043.unfold_attr);
                               unfold_tac = (uu___155_13043.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_13043.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_13043.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_13043.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_13043.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_13043.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_13043.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_13045 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_13045.tcenv);
                               debug = (uu___156_13045.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_13045.primitive_steps);
                               strong = (uu___156_13045.strong);
                               memoize_lazy = (uu___156_13045.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_13045.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13047 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13047 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13079  -> dummy :: env1) env)
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
                                          let uu____13120 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13120)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_13125 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_13125.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_13125.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13126 -> lopt  in
                           (log cfg
                              (fun uu____13132  ->
                                 let uu____13133 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13133);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_13142 = cfg  in
                               {
                                 steps = (uu___158_13142.steps);
                                 tcenv = (uu___158_13142.tcenv);
                                 debug = (uu___158_13142.debug);
                                 delta_level = (uu___158_13142.delta_level);
                                 primitive_steps =
                                   (uu___158_13142.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_13142.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_13142.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____13145)::uu____13146 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___155_13158 = cfg.steps  in
                             {
                               beta = (uu___155_13158.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_13158.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_13158.unfold_until);
                               unfold_only = (uu___155_13158.unfold_only);
                               unfold_fully = (uu___155_13158.unfold_fully);
                               unfold_attr = (uu___155_13158.unfold_attr);
                               unfold_tac = (uu___155_13158.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_13158.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_13158.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_13158.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_13158.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_13158.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_13158.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_13160 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_13160.tcenv);
                               debug = (uu___156_13160.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_13160.primitive_steps);
                               strong = (uu___156_13160.strong);
                               memoize_lazy = (uu___156_13160.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_13160.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13162 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13162 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13194  -> dummy :: env1) env)
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
                                          let uu____13235 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13235)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_13240 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_13240.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_13240.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13241 -> lopt  in
                           (log cfg
                              (fun uu____13247  ->
                                 let uu____13248 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13248);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_13257 = cfg  in
                               {
                                 steps = (uu___158_13257.steps);
                                 tcenv = (uu___158_13257.tcenv);
                                 debug = (uu___158_13257.debug);
                                 delta_level = (uu___158_13257.delta_level);
                                 primitive_steps =
                                   (uu___158_13257.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_13257.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_13257.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13260)::uu____13261 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___155_13275 = cfg.steps  in
                             {
                               beta = (uu___155_13275.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_13275.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_13275.unfold_until);
                               unfold_only = (uu___155_13275.unfold_only);
                               unfold_fully = (uu___155_13275.unfold_fully);
                               unfold_attr = (uu___155_13275.unfold_attr);
                               unfold_tac = (uu___155_13275.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_13275.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_13275.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_13275.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_13275.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_13275.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_13275.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_13277 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_13277.tcenv);
                               debug = (uu___156_13277.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_13277.primitive_steps);
                               strong = (uu___156_13277.strong);
                               memoize_lazy = (uu___156_13277.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_13277.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13279 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13279 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13311  -> dummy :: env1) env)
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
                                          let uu____13352 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13352)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_13357 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_13357.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_13357.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13358 -> lopt  in
                           (log cfg
                              (fun uu____13364  ->
                                 let uu____13365 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13365);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_13374 = cfg  in
                               {
                                 steps = (uu___158_13374.steps);
                                 tcenv = (uu___158_13374.tcenv);
                                 debug = (uu___158_13374.debug);
                                 delta_level = (uu___158_13374.delta_level);
                                 primitive_steps =
                                   (uu___158_13374.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_13374.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_13374.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13377)::uu____13378 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___155_13392 = cfg.steps  in
                             {
                               beta = (uu___155_13392.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_13392.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_13392.unfold_until);
                               unfold_only = (uu___155_13392.unfold_only);
                               unfold_fully = (uu___155_13392.unfold_fully);
                               unfold_attr = (uu___155_13392.unfold_attr);
                               unfold_tac = (uu___155_13392.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_13392.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_13392.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_13392.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_13392.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_13392.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_13392.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_13394 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_13394.tcenv);
                               debug = (uu___156_13394.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_13394.primitive_steps);
                               strong = (uu___156_13394.strong);
                               memoize_lazy = (uu___156_13394.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_13394.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13396 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13396 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13428  -> dummy :: env1) env)
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
                                          let uu____13469 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13469)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_13474 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_13474.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_13474.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13475 -> lopt  in
                           (log cfg
                              (fun uu____13481  ->
                                 let uu____13482 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13482);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_13491 = cfg  in
                               {
                                 steps = (uu___158_13491.steps);
                                 tcenv = (uu___158_13491.tcenv);
                                 debug = (uu___158_13491.debug);
                                 delta_level = (uu___158_13491.delta_level);
                                 primitive_steps =
                                   (uu___158_13491.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_13491.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_13491.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13494)::uu____13495 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___155_13513 = cfg.steps  in
                             {
                               beta = (uu___155_13513.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_13513.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_13513.unfold_until);
                               unfold_only = (uu___155_13513.unfold_only);
                               unfold_fully = (uu___155_13513.unfold_fully);
                               unfold_attr = (uu___155_13513.unfold_attr);
                               unfold_tac = (uu___155_13513.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_13513.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_13513.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_13513.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_13513.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_13513.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_13513.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_13515 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_13515.tcenv);
                               debug = (uu___156_13515.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_13515.primitive_steps);
                               strong = (uu___156_13515.strong);
                               memoize_lazy = (uu___156_13515.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_13515.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13517 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13517 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13549  -> dummy :: env1) env)
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
                                          let uu____13590 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13590)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_13595 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_13595.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_13595.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13596 -> lopt  in
                           (log cfg
                              (fun uu____13602  ->
                                 let uu____13603 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13603);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_13612 = cfg  in
                               {
                                 steps = (uu___158_13612.steps);
                                 tcenv = (uu___158_13612.tcenv);
                                 debug = (uu___158_13612.debug);
                                 delta_level = (uu___158_13612.delta_level);
                                 primitive_steps =
                                   (uu___158_13612.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_13612.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_13612.normalize_pure_lets)
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
                             let uu___155_13618 = cfg.steps  in
                             {
                               beta = (uu___155_13618.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_13618.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_13618.unfold_until);
                               unfold_only = (uu___155_13618.unfold_only);
                               unfold_fully = (uu___155_13618.unfold_fully);
                               unfold_attr = (uu___155_13618.unfold_attr);
                               unfold_tac = (uu___155_13618.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_13618.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_13618.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_13618.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_13618.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_13618.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_13618.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_13620 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_13620.tcenv);
                               debug = (uu___156_13620.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_13620.primitive_steps);
                               strong = (uu___156_13620.strong);
                               memoize_lazy = (uu___156_13620.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_13620.normalize_pure_lets)
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
                                     fun uu____13654  -> dummy :: env1) env)
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
                                          let uu____13695 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13695)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_13700 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_13700.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_13700.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13701 -> lopt  in
                           (log cfg
                              (fun uu____13707  ->
                                 let uu____13708 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13708);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_13717 = cfg  in
                               {
                                 steps = (uu___158_13717.steps);
                                 tcenv = (uu___158_13717.tcenv);
                                 debug = (uu___158_13717.debug);
                                 delta_level = (uu___158_13717.delta_level);
                                 primitive_steps =
                                   (uu___158_13717.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_13717.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_13717.normalize_pure_lets)
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
                      (fun uu____13756  ->
                         fun stack1  ->
                           match uu____13756 with
                           | (a,aq) ->
                               let uu____13768 =
                                 let uu____13769 =
                                   let uu____13776 =
                                     let uu____13777 =
                                       let uu____13808 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____13808, false)  in
                                     Clos uu____13777  in
                                   (uu____13776, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____13769  in
                               uu____13768 :: stack1) args)
                  in
               (log cfg
                  (fun uu____13896  ->
                     let uu____13897 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13897);
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
                             ((let uu___159_13943 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___159_13943.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___159_13943.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____13944 ->
                      let uu____13959 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13959)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____13962 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____13962 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____13987 =
                          let uu____13988 =
                            let uu____13995 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___160_14001 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___160_14001.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___160_14001.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13995)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____13988  in
                        mk uu____13987 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____14020 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____14020
               else
                 (let uu____14022 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____14022 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____14030 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____14052  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____14030 c1  in
                      let t2 =
                        let uu____14074 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____14074 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14185)::uu____14186 ->
                    (log cfg
                       (fun uu____14199  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14200)::uu____14201 ->
                    (log cfg
                       (fun uu____14212  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14213,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14214;
                                   FStar_Syntax_Syntax.vars = uu____14215;_},uu____14216,uu____14217))::uu____14218
                    ->
                    (log cfg
                       (fun uu____14225  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14226)::uu____14227 ->
                    (log cfg
                       (fun uu____14238  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14239 ->
                    (log cfg
                       (fun uu____14242  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14246  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14271 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14271
                         | FStar_Util.Inr c ->
                             let uu____14281 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14281
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14300 =
                               let uu____14301 =
                                 let uu____14328 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14328, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14301
                                in
                             mk uu____14300 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14363 ->
                           let uu____14364 =
                             let uu____14365 =
                               let uu____14366 =
                                 let uu____14393 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14393, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14366
                                in
                             mk uu____14365 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14364))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 if
                   ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee)
                     && (Prims.op_Negation (cfg.steps).weak)
                 then
                   let uu___161_14470 = cfg  in
                   {
                     steps =
                       (let uu___162_14473 = cfg.steps  in
                        {
                          beta = (uu___162_14473.beta);
                          iota = (uu___162_14473.iota);
                          zeta = (uu___162_14473.zeta);
                          weak = true;
                          hnf = (uu___162_14473.hnf);
                          primops = (uu___162_14473.primops);
                          do_not_unfold_pure_lets =
                            (uu___162_14473.do_not_unfold_pure_lets);
                          unfold_until = (uu___162_14473.unfold_until);
                          unfold_only = (uu___162_14473.unfold_only);
                          unfold_fully = (uu___162_14473.unfold_fully);
                          unfold_attr = (uu___162_14473.unfold_attr);
                          unfold_tac = (uu___162_14473.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___162_14473.pure_subterms_within_computations);
                          simplify = (uu___162_14473.simplify);
                          erase_universes = (uu___162_14473.erase_universes);
                          allow_unbound_universes =
                            (uu___162_14473.allow_unbound_universes);
                          reify_ = (uu___162_14473.reify_);
                          compress_uvars = (uu___162_14473.compress_uvars);
                          no_full_norm = (uu___162_14473.no_full_norm);
                          check_no_uvars = (uu___162_14473.check_no_uvars);
                          unmeta = (uu___162_14473.unmeta);
                          unascribe = (uu___162_14473.unascribe);
                          in_full_norm_request =
                            (uu___162_14473.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___162_14473.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___161_14470.tcenv);
                     debug = (uu___161_14470.debug);
                     delta_level = (uu___161_14470.delta_level);
                     primitive_steps = (uu___161_14470.primitive_steps);
                     strong = (uu___161_14470.strong);
                     memoize_lazy = (uu___161_14470.memoize_lazy);
                     normalize_pure_lets =
                       (uu___161_14470.normalize_pure_lets)
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
                         let uu____14509 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14509 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___163_14529 = cfg  in
                               let uu____14530 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___163_14529.steps);
                                 tcenv = uu____14530;
                                 debug = (uu___163_14529.debug);
                                 delta_level = (uu___163_14529.delta_level);
                                 primitive_steps =
                                   (uu___163_14529.primitive_steps);
                                 strong = (uu___163_14529.strong);
                                 memoize_lazy = (uu___163_14529.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___163_14529.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14537 =
                                 let uu____14538 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14538  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14537
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___164_14541 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___164_14541.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___164_14541.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___164_14541.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___164_14541.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____14542 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14542
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14553,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14554;
                               FStar_Syntax_Syntax.lbunivs = uu____14555;
                               FStar_Syntax_Syntax.lbtyp = uu____14556;
                               FStar_Syntax_Syntax.lbeff = uu____14557;
                               FStar_Syntax_Syntax.lbdef = uu____14558;
                               FStar_Syntax_Syntax.lbattrs = uu____14559;
                               FStar_Syntax_Syntax.lbpos = uu____14560;_}::uu____14561),uu____14562)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14602 =
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
               if uu____14602
               then
                 let binder =
                   let uu____14604 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14604  in
                 let env1 =
                   let uu____14614 =
                     let uu____14621 =
                       let uu____14622 =
                         let uu____14653 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14653,
                           false)
                          in
                       Clos uu____14622  in
                     ((FStar_Pervasives_Native.Some binder), uu____14621)  in
                   uu____14614 :: env  in
                 (log cfg
                    (fun uu____14748  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____14752  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14753 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14753))
                 else
                   (let uu____14755 =
                      let uu____14760 =
                        let uu____14761 =
                          let uu____14766 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14766
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14761]  in
                      FStar_Syntax_Subst.open_term uu____14760 body  in
                    match uu____14755 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14787  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14795 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14795  in
                            FStar_Util.Inl
                              (let uu___165_14805 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___165_14805.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___165_14805.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____14808  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___166_14810 = lb  in
                             let uu____14811 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___166_14810.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___166_14810.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14811;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___166_14810.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___166_14810.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14836  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___167_14859 = cfg  in
                             {
                               steps = (uu___167_14859.steps);
                               tcenv = (uu___167_14859.tcenv);
                               debug = (uu___167_14859.debug);
                               delta_level = (uu___167_14859.delta_level);
                               primitive_steps =
                                 (uu___167_14859.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___167_14859.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___167_14859.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____14862  ->
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
               let uu____14879 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____14879 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____14915 =
                               let uu___168_14916 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___168_14916.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___168_14916.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____14915  in
                           let uu____14917 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____14917 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____14943 =
                                   FStar_List.map (fun uu____14959  -> dummy)
                                     lbs1
                                    in
                                 let uu____14960 =
                                   let uu____14969 =
                                     FStar_List.map
                                       (fun uu____14989  -> dummy) xs1
                                      in
                                   FStar_List.append uu____14969 env  in
                                 FStar_List.append uu____14943 uu____14960
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____15013 =
                                       let uu___169_15014 = rc  in
                                       let uu____15015 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___169_15014.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____15015;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___169_15014.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____15013
                                 | uu____15024 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___170_15030 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___170_15030.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___170_15030.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___170_15030.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___170_15030.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____15040 =
                        FStar_List.map (fun uu____15056  -> dummy) lbs2  in
                      FStar_List.append uu____15040 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____15064 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____15064 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___171_15080 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___171_15080.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___171_15080.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____15109 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____15109
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____15128 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15204  ->
                        match uu____15204 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___172_15325 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___172_15325.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___172_15325.FStar_Syntax_Syntax.sort)
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
               (match uu____15128 with
                | (rec_env,memos,uu____15552) ->
                    let uu____15605 =
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
                             let uu____15928 =
                               let uu____15935 =
                                 let uu____15936 =
                                   let uu____15967 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15967, false)
                                    in
                                 Clos uu____15936  in
                               (FStar_Pervasives_Native.None, uu____15935)
                                in
                             uu____15928 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____16071  ->
                     let uu____16072 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____16072);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____16094 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____16096::uu____16097 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____16102) ->
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
                             | uu____16125 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____16139 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____16139
                              | uu____16150 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____16156 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16182 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16184 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____16185 =
                        let uu____16186 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16187 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16186 uu____16187
                         in
                      failwith uu____16185
                    else rebuild cfg env stack t2
                | uu____16189 -> norm cfg env stack t2))

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
                let uu____16199 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16199  in
              let uu____16200 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16200 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16213  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16224  ->
                        let uu____16225 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16226 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16225 uu____16226);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____16231 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____16231 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____16240))::stack1 ->
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
                      | uu____16279 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____16282 ->
                          let uu____16285 =
                            let uu____16286 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16286
                             in
                          failwith uu____16285
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
                  let uu___173_16310 = cfg  in
                  let uu____16311 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____16311;
                    tcenv = (uu___173_16310.tcenv);
                    debug = (uu___173_16310.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___173_16310.primitive_steps);
                    strong = (uu___173_16310.strong);
                    memoize_lazy = (uu___173_16310.memoize_lazy);
                    normalize_pure_lets =
                      (uu___173_16310.normalize_pure_lets)
                  }
                else
                  (let uu___174_16313 = cfg  in
                   {
                     steps =
                       (let uu___175_16316 = cfg.steps  in
                        {
                          beta = (uu___175_16316.beta);
                          iota = (uu___175_16316.iota);
                          zeta = false;
                          weak = (uu___175_16316.weak);
                          hnf = (uu___175_16316.hnf);
                          primops = (uu___175_16316.primops);
                          do_not_unfold_pure_lets =
                            (uu___175_16316.do_not_unfold_pure_lets);
                          unfold_until = (uu___175_16316.unfold_until);
                          unfold_only = (uu___175_16316.unfold_only);
                          unfold_fully = (uu___175_16316.unfold_fully);
                          unfold_attr = (uu___175_16316.unfold_attr);
                          unfold_tac = (uu___175_16316.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___175_16316.pure_subterms_within_computations);
                          simplify = (uu___175_16316.simplify);
                          erase_universes = (uu___175_16316.erase_universes);
                          allow_unbound_universes =
                            (uu___175_16316.allow_unbound_universes);
                          reify_ = (uu___175_16316.reify_);
                          compress_uvars = (uu___175_16316.compress_uvars);
                          no_full_norm = (uu___175_16316.no_full_norm);
                          check_no_uvars = (uu___175_16316.check_no_uvars);
                          unmeta = (uu___175_16316.unmeta);
                          unascribe = (uu___175_16316.unascribe);
                          in_full_norm_request =
                            (uu___175_16316.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___175_16316.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___174_16313.tcenv);
                     debug = (uu___174_16313.debug);
                     delta_level = (uu___174_16313.delta_level);
                     primitive_steps = (uu___174_16313.primitive_steps);
                     strong = (uu___174_16313.strong);
                     memoize_lazy = (uu___174_16313.memoize_lazy);
                     normalize_pure_lets =
                       (uu___174_16313.normalize_pure_lets)
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
                  (fun uu____16350  ->
                     let uu____16351 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16352 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16351
                       uu____16352);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____16354 =
                   let uu____16355 = FStar_Syntax_Subst.compress head3  in
                   uu____16355.FStar_Syntax_Syntax.n  in
                 match uu____16354 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____16373 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16373
                        in
                     let uu____16374 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16374 with
                      | (uu____16375,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16385 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16395 =
                                   let uu____16396 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16396.FStar_Syntax_Syntax.n  in
                                 match uu____16395 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16402,uu____16403))
                                     ->
                                     let uu____16412 =
                                       let uu____16413 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16413.FStar_Syntax_Syntax.n  in
                                     (match uu____16412 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16419,msrc,uu____16421))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16430 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16430
                                      | uu____16431 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16432 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16433 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16433 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___176_16438 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___176_16438.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___176_16438.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___176_16438.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___176_16438.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___176_16438.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____16439 = FStar_List.tl stack  in
                                    let uu____16440 =
                                      let uu____16441 =
                                        let uu____16448 =
                                          let uu____16449 =
                                            let uu____16462 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16462)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16449
                                           in
                                        FStar_Syntax_Syntax.mk uu____16448
                                         in
                                      uu____16441
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16439 uu____16440
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16478 =
                                      let uu____16479 = is_return body  in
                                      match uu____16479 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16483;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16484;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16487 -> false  in
                                    if uu____16478
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
                                         let uu____16508 =
                                           let uu____16515 =
                                             let uu____16516 =
                                               let uu____16533 =
                                                 let uu____16540 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16540]  in
                                               (uu____16533, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16516
                                              in
                                           FStar_Syntax_Syntax.mk uu____16515
                                            in
                                         uu____16508
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16574 =
                                           let uu____16575 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16575.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16574 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16581::uu____16582::[])
                                             ->
                                             let uu____16587 =
                                               let uu____16594 =
                                                 let uu____16595 =
                                                   let uu____16602 =
                                                     let uu____16603 =
                                                       let uu____16604 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16604
                                                        in
                                                     let uu____16605 =
                                                       let uu____16608 =
                                                         let uu____16609 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16609
                                                          in
                                                       [uu____16608]  in
                                                     uu____16603 ::
                                                       uu____16605
                                                      in
                                                   (bind1, uu____16602)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16595
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16594
                                                in
                                             uu____16587
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16615 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____16627 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____16627
                                         then
                                           let uu____16636 =
                                             let uu____16643 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16643
                                              in
                                           let uu____16644 =
                                             let uu____16653 =
                                               let uu____16660 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____16660
                                                in
                                             [uu____16653]  in
                                           uu____16636 :: uu____16644
                                         else []  in
                                       let reified =
                                         let uu____16689 =
                                           let uu____16696 =
                                             let uu____16697 =
                                               let uu____16712 =
                                                 let uu____16721 =
                                                   let uu____16730 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____16737 =
                                                     let uu____16746 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____16746]  in
                                                   uu____16730 :: uu____16737
                                                    in
                                                 let uu____16771 =
                                                   let uu____16780 =
                                                     let uu____16789 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16796 =
                                                       let uu____16805 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____16812 =
                                                         let uu____16821 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____16828 =
                                                           let uu____16837 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____16837]  in
                                                         uu____16821 ::
                                                           uu____16828
                                                          in
                                                       uu____16805 ::
                                                         uu____16812
                                                        in
                                                     uu____16789 ::
                                                       uu____16796
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____16780
                                                    in
                                                 FStar_List.append
                                                   uu____16721 uu____16771
                                                  in
                                               (bind_inst, uu____16712)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16697
                                              in
                                           FStar_Syntax_Syntax.mk uu____16696
                                            in
                                         uu____16689
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____16903  ->
                                            let uu____16904 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____16905 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____16904 uu____16905);
                                       (let uu____16906 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____16906 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____16930 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16930
                        in
                     let uu____16931 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16931 with
                      | (uu____16932,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____16969 =
                                  let uu____16970 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____16970.FStar_Syntax_Syntax.n  in
                                match uu____16969 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____16974) -> t2
                                | uu____16979 -> head4  in
                              let uu____16980 =
                                let uu____16981 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____16981.FStar_Syntax_Syntax.n  in
                              match uu____16980 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____16987 -> FStar_Pervasives_Native.None
                               in
                            let uu____16988 = maybe_extract_fv head4  in
                            match uu____16988 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____16998 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____16998
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____17003 = maybe_extract_fv head5
                                     in
                                  match uu____17003 with
                                  | FStar_Pervasives_Native.Some uu____17008
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____17009 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____17014 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____17029 =
                              match uu____17029 with
                              | (e,q) ->
                                  let uu____17036 =
                                    let uu____17037 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____17037.FStar_Syntax_Syntax.n  in
                                  (match uu____17036 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____17052 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____17052
                                   | uu____17053 -> false)
                               in
                            let uu____17054 =
                              let uu____17055 =
                                let uu____17064 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____17064 :: args  in
                              FStar_Util.for_some is_arg_impure uu____17055
                               in
                            if uu____17054
                            then
                              let uu____17083 =
                                let uu____17084 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____17084
                                 in
                              failwith uu____17083
                            else ());
                           (let uu____17086 = maybe_unfold_action head_app
                               in
                            match uu____17086 with
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
                                   (fun uu____17129  ->
                                      let uu____17130 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____17131 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____17130 uu____17131);
                                 (let uu____17132 = FStar_List.tl stack  in
                                  norm cfg env uu____17132 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____17134) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____17158 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____17158  in
                     (log cfg
                        (fun uu____17162  ->
                           let uu____17163 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____17163);
                      (let uu____17164 = FStar_List.tl stack  in
                       norm cfg env uu____17164 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____17285  ->
                               match uu____17285 with
                               | (pat,wopt,tm) ->
                                   let uu____17333 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____17333)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____17365 = FStar_List.tl stack  in
                     norm cfg env uu____17365 tm
                 | uu____17366 -> fallback ())

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
              (fun uu____17380  ->
                 let uu____17381 = FStar_Ident.string_of_lid msrc  in
                 let uu____17382 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17383 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17381
                   uu____17382 uu____17383);
            (let uu____17384 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____17384
             then
               let ed =
                 let uu____17386 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____17386  in
               let uu____17387 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____17387 with
               | (uu____17388,return_repr) ->
                   let return_inst =
                     let uu____17401 =
                       let uu____17402 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17402.FStar_Syntax_Syntax.n  in
                     match uu____17401 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17408::[]) ->
                         let uu____17413 =
                           let uu____17420 =
                             let uu____17421 =
                               let uu____17428 =
                                 let uu____17429 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17429]  in
                               (return_tm, uu____17428)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17421  in
                           FStar_Syntax_Syntax.mk uu____17420  in
                         uu____17413 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17435 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17438 =
                     let uu____17445 =
                       let uu____17446 =
                         let uu____17461 =
                           let uu____17470 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17477 =
                             let uu____17486 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17486]  in
                           uu____17470 :: uu____17477  in
                         (return_inst, uu____17461)  in
                       FStar_Syntax_Syntax.Tm_app uu____17446  in
                     FStar_Syntax_Syntax.mk uu____17445  in
                   uu____17438 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17525 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17525 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17528 =
                      let uu____17529 = FStar_Ident.text_of_lid msrc  in
                      let uu____17530 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17529 uu____17530
                       in
                    failwith uu____17528
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17531;
                      FStar_TypeChecker_Env.mtarget = uu____17532;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17533;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17555 =
                      let uu____17556 = FStar_Ident.text_of_lid msrc  in
                      let uu____17557 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17556 uu____17557
                       in
                    failwith uu____17555
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17558;
                      FStar_TypeChecker_Env.mtarget = uu____17559;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17560;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____17595 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____17596 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____17595 t FStar_Syntax_Syntax.tun uu____17596))

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
                (fun uu____17652  ->
                   match uu____17652 with
                   | (a,imp) ->
                       let uu____17663 = norm cfg env [] a  in
                       (uu____17663, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____17671  ->
             let uu____17672 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17673 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____17672 uu____17673);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17697 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____17697
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___177_17700 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___177_17700.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___177_17700.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17722 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____17722
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___178_17725 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___178_17725.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___178_17725.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17762  ->
                      match uu____17762 with
                      | (a,i) ->
                          let uu____17773 = norm cfg env [] a  in
                          (uu____17773, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___92_17791  ->
                       match uu___92_17791 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17795 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17795
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___179_17803 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___180_17806 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___180_17806.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___179_17803.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___179_17803.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17809  ->
        match uu____17809 with
        | (x,imp) ->
            let uu____17812 =
              let uu___181_17813 = x  in
              let uu____17814 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___181_17813.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___181_17813.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17814
              }  in
            (uu____17812, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17820 =
          FStar_List.fold_left
            (fun uu____17854  ->
               fun b  ->
                 match uu____17854 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17820 with | (nbs,uu____17934) -> FStar_List.rev nbs

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
            let uu____17966 =
              let uu___182_17967 = rc  in
              let uu____17968 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___182_17967.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17968;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___182_17967.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17966
        | uu____17977 -> lopt

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
            (let uu____17998 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17999 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____17998
               uu____17999)
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
          let uu____18021 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____18021
          then tm1
          else
            (let w t =
               let uu___183_18035 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___183_18035.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___183_18035.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____18046 =
                 let uu____18047 = FStar_Syntax_Util.unmeta t  in
                 uu____18047.FStar_Syntax_Syntax.n  in
               match uu____18046 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____18054 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____18103)::args1,(bv,uu____18106)::bs1) ->
                   let uu____18140 =
                     let uu____18141 = FStar_Syntax_Subst.compress t  in
                     uu____18141.FStar_Syntax_Syntax.n  in
                   (match uu____18140 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____18145 -> false)
               | ([],[]) -> true
               | (uu____18166,uu____18167) -> false  in
             let is_applied bs t =
               let uu____18207 = FStar_Syntax_Util.head_and_args' t  in
               match uu____18207 with
               | (hd1,args) ->
                   let uu____18240 =
                     let uu____18241 = FStar_Syntax_Subst.compress hd1  in
                     uu____18241.FStar_Syntax_Syntax.n  in
                   (match uu____18240 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____18247 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____18263 = FStar_Syntax_Util.is_squash t  in
               match uu____18263 with
               | FStar_Pervasives_Native.Some (uu____18274,t') ->
                   is_applied bs t'
               | uu____18286 ->
                   let uu____18295 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____18295 with
                    | FStar_Pervasives_Native.Some (uu____18306,t') ->
                        is_applied bs t'
                    | uu____18318 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____18337 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18337 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18344)::(q,uu____18346)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____18373 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____18373 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____18378 =
                          let uu____18379 = FStar_Syntax_Subst.compress p  in
                          uu____18379.FStar_Syntax_Syntax.n  in
                        (match uu____18378 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____18385 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____18385
                         | uu____18388 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____18391)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____18408 =
                          let uu____18409 = FStar_Syntax_Subst.compress p1
                             in
                          uu____18409.FStar_Syntax_Syntax.n  in
                        (match uu____18408 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____18415 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____18415
                         | uu____18418 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____18422 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____18422 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____18427 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____18427 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____18436 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____18436
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____18441)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____18458 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____18458 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____18467 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____18467
                              | uu____18470 -> FStar_Pervasives_Native.None)
                         | uu____18473 -> FStar_Pervasives_Native.None)
                    | uu____18476 -> FStar_Pervasives_Native.None)
               | uu____18479 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18492 =
                 let uu____18493 = FStar_Syntax_Subst.compress phi  in
                 uu____18493.FStar_Syntax_Syntax.n  in
               match uu____18492 with
               | FStar_Syntax_Syntax.Tm_match (uu____18498,br::brs) ->
                   let uu____18565 = br  in
                   (match uu____18565 with
                    | (uu____18582,uu____18583,e) ->
                        let r =
                          let uu____18604 = simp_t e  in
                          match uu____18604 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18610 =
                                FStar_List.for_all
                                  (fun uu____18628  ->
                                     match uu____18628 with
                                     | (uu____18641,uu____18642,e') ->
                                         let uu____18656 = simp_t e'  in
                                         uu____18656 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18610
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18664 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18673 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18673
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18704 =
                 match uu____18704 with
                 | (t1,q) ->
                     let uu____18717 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18717 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18745 -> (t1, q))
                  in
               let uu____18754 = FStar_Syntax_Util.head_and_args t  in
               match uu____18754 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18814 =
                 let uu____18815 = FStar_Syntax_Util.unmeta ty  in
                 uu____18815.FStar_Syntax_Syntax.n  in
               match uu____18814 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18819) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18824,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18844 -> false  in
             let simplify1 arg =
               let uu____18869 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18869, arg)  in
             let uu____18878 = is_quantified_const tm1  in
             match uu____18878 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____18882 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____18882
             | FStar_Pervasives_Native.None  ->
                 let uu____18883 =
                   let uu____18884 = FStar_Syntax_Subst.compress tm1  in
                   uu____18884.FStar_Syntax_Syntax.n  in
                 (match uu____18883 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18888;
                              FStar_Syntax_Syntax.vars = uu____18889;_},uu____18890);
                         FStar_Syntax_Syntax.pos = uu____18891;
                         FStar_Syntax_Syntax.vars = uu____18892;_},args)
                      ->
                      let uu____18918 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18918
                      then
                        let uu____18919 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18919 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18964)::
                             (uu____18965,(arg,uu____18967))::[] ->
                             maybe_auto_squash arg
                         | (uu____19016,(arg,uu____19018))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19019)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19068)::uu____19069::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19120::(FStar_Pervasives_Native.Some (false
                                         ),uu____19121)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19172 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19186 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19186
                         then
                           let uu____19187 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19187 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19232)::uu____19233::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19284::(FStar_Pervasives_Native.Some (true
                                           ),uu____19285)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19336)::(uu____19337,(arg,uu____19339))::[]
                               -> maybe_auto_squash arg
                           | (uu____19388,(arg,uu____19390))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19391)::[]
                               -> maybe_auto_squash arg
                           | uu____19440 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19454 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19454
                            then
                              let uu____19455 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19455 with
                              | uu____19500::(FStar_Pervasives_Native.Some
                                              (true ),uu____19501)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19552)::uu____19553::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19604)::(uu____19605,(arg,uu____19607))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19656,(p,uu____19658))::(uu____19659,
                                                                (q,uu____19661))::[]
                                  ->
                                  let uu____19708 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19708
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19710 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19724 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19724
                               then
                                 let uu____19725 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19725 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19770)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19771)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19822)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19823)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19874)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19875)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19926)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19927)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19978,(arg,uu____19980))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19981)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20030)::(uu____20031,(arg,uu____20033))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20082,(arg,uu____20084))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20085)::[]
                                     ->
                                     let uu____20134 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20134
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20135)::(uu____20136,(arg,uu____20138))::[]
                                     ->
                                     let uu____20187 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20187
                                 | (uu____20188,(p,uu____20190))::(uu____20191,
                                                                   (q,uu____20193))::[]
                                     ->
                                     let uu____20240 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20240
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20242 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20256 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20256
                                  then
                                    let uu____20257 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20257 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20302)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20333)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20364 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20378 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20378
                                     then
                                       match args with
                                       | (t,uu____20380)::[] ->
                                           let uu____20397 =
                                             let uu____20398 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20398.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20397 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20401::[],body,uu____20403)
                                                ->
                                                let uu____20430 = simp_t body
                                                   in
                                                (match uu____20430 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20433 -> tm1)
                                            | uu____20436 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20438))::(t,uu____20440)::[]
                                           ->
                                           let uu____20467 =
                                             let uu____20468 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20468.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20467 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20471::[],body,uu____20473)
                                                ->
                                                let uu____20500 = simp_t body
                                                   in
                                                (match uu____20500 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20503 -> tm1)
                                            | uu____20506 -> tm1)
                                       | uu____20507 -> tm1
                                     else
                                       (let uu____20517 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20517
                                        then
                                          match args with
                                          | (t,uu____20519)::[] ->
                                              let uu____20536 =
                                                let uu____20537 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20537.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20536 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20540::[],body,uu____20542)
                                                   ->
                                                   let uu____20569 =
                                                     simp_t body  in
                                                   (match uu____20569 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20572 -> tm1)
                                               | uu____20575 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20577))::(t,uu____20579)::[]
                                              ->
                                              let uu____20606 =
                                                let uu____20607 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20607.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20606 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20610::[],body,uu____20612)
                                                   ->
                                                   let uu____20639 =
                                                     simp_t body  in
                                                   (match uu____20639 with
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
                                                    | uu____20642 -> tm1)
                                               | uu____20645 -> tm1)
                                          | uu____20646 -> tm1
                                        else
                                          (let uu____20656 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20656
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20657;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20658;_},uu____20659)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20676;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20677;_},uu____20678)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20695 -> tm1
                                           else
                                             (let uu____20705 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20705 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20725 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20735;
                         FStar_Syntax_Syntax.vars = uu____20736;_},args)
                      ->
                      let uu____20758 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20758
                      then
                        let uu____20759 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20759 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20804)::
                             (uu____20805,(arg,uu____20807))::[] ->
                             maybe_auto_squash arg
                         | (uu____20856,(arg,uu____20858))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20859)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20908)::uu____20909::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20960::(FStar_Pervasives_Native.Some (false
                                         ),uu____20961)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21012 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21026 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21026
                         then
                           let uu____21027 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21027 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21072)::uu____21073::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21124::(FStar_Pervasives_Native.Some (true
                                           ),uu____21125)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21176)::(uu____21177,(arg,uu____21179))::[]
                               -> maybe_auto_squash arg
                           | (uu____21228,(arg,uu____21230))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21231)::[]
                               -> maybe_auto_squash arg
                           | uu____21280 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21294 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21294
                            then
                              let uu____21295 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21295 with
                              | uu____21340::(FStar_Pervasives_Native.Some
                                              (true ),uu____21341)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21392)::uu____21393::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21444)::(uu____21445,(arg,uu____21447))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21496,(p,uu____21498))::(uu____21499,
                                                                (q,uu____21501))::[]
                                  ->
                                  let uu____21548 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21548
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21550 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21564 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21564
                               then
                                 let uu____21565 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21565 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21610)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21611)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21662)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21663)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21714)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21715)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21766)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21767)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21818,(arg,uu____21820))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21821)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21870)::(uu____21871,(arg,uu____21873))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21922,(arg,uu____21924))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21925)::[]
                                     ->
                                     let uu____21974 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21974
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21975)::(uu____21976,(arg,uu____21978))::[]
                                     ->
                                     let uu____22027 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22027
                                 | (uu____22028,(p,uu____22030))::(uu____22031,
                                                                   (q,uu____22033))::[]
                                     ->
                                     let uu____22080 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22080
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22082 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22096 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22096
                                  then
                                    let uu____22097 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22097 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22142)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22173)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22204 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22218 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22218
                                     then
                                       match args with
                                       | (t,uu____22220)::[] ->
                                           let uu____22237 =
                                             let uu____22238 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22238.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22237 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22241::[],body,uu____22243)
                                                ->
                                                let uu____22270 = simp_t body
                                                   in
                                                (match uu____22270 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22273 -> tm1)
                                            | uu____22276 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22278))::(t,uu____22280)::[]
                                           ->
                                           let uu____22307 =
                                             let uu____22308 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22308.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22307 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22311::[],body,uu____22313)
                                                ->
                                                let uu____22340 = simp_t body
                                                   in
                                                (match uu____22340 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22343 -> tm1)
                                            | uu____22346 -> tm1)
                                       | uu____22347 -> tm1
                                     else
                                       (let uu____22357 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22357
                                        then
                                          match args with
                                          | (t,uu____22359)::[] ->
                                              let uu____22376 =
                                                let uu____22377 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22377.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22376 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22380::[],body,uu____22382)
                                                   ->
                                                   let uu____22409 =
                                                     simp_t body  in
                                                   (match uu____22409 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22412 -> tm1)
                                               | uu____22415 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22417))::(t,uu____22419)::[]
                                              ->
                                              let uu____22446 =
                                                let uu____22447 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22447.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22446 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22450::[],body,uu____22452)
                                                   ->
                                                   let uu____22479 =
                                                     simp_t body  in
                                                   (match uu____22479 with
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
                                                    | uu____22482 -> tm1)
                                               | uu____22485 -> tm1)
                                          | uu____22486 -> tm1
                                        else
                                          (let uu____22496 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22496
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22497;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22498;_},uu____22499)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22516;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22517;_},uu____22518)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22535 -> tm1
                                           else
                                             (let uu____22545 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22545 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22565 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____22580 = simp_t t  in
                      (match uu____22580 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22583 ->
                      let uu____22606 = is_const_match tm1  in
                      (match uu____22606 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____22609 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____22619  ->
               (let uu____22621 = FStar_Syntax_Print.tag_of_term t  in
                let uu____22622 = FStar_Syntax_Print.term_to_string t  in
                let uu____22623 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____22630 =
                  let uu____22631 =
                    let uu____22634 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____22634
                     in
                  stack_to_string uu____22631  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____22621 uu____22622 uu____22623 uu____22630);
               (let uu____22657 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____22657
                then
                  let uu____22658 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____22658 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____22665 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____22666 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____22667 =
                          let uu____22668 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____22668
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____22665
                          uu____22666 uu____22667);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____22686 =
                     let uu____22687 =
                       let uu____22688 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____22688  in
                     FStar_Util.string_of_int uu____22687  in
                   let uu____22693 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____22694 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____22686 uu____22693 uu____22694)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____22700,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____22751  ->
                     let uu____22752 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____22752);
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
               let uu____22790 =
                 let uu___184_22791 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___184_22791.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___184_22791.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____22790
           | (Arg (Univ uu____22794,uu____22795,uu____22796))::uu____22797 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____22800,uu____22801))::uu____22802 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____22817,uu____22818),aq,r))::stack1
               when
               let uu____22868 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____22868 ->
               let t2 =
                 let uu____22872 =
                   let uu____22877 =
                     let uu____22878 = closure_as_term cfg env_arg tm  in
                     (uu____22878, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____22877  in
                 uu____22872 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____22888),aq,r))::stack1 ->
               (log cfg
                  (fun uu____22941  ->
                     let uu____22942 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____22942);
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
                  (let uu____22954 = FStar_ST.op_Bang m  in
                   match uu____22954 with
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
                   | FStar_Pervasives_Native.Some (uu____23097,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____23150 =
                 log cfg
                   (fun uu____23154  ->
                      let uu____23155 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____23155);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____23161 =
                 let uu____23162 = FStar_Syntax_Subst.compress t1  in
                 uu____23162.FStar_Syntax_Syntax.n  in
               (match uu____23161 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____23189 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____23189  in
                    (log cfg
                       (fun uu____23193  ->
                          let uu____23194 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____23194);
                     (let uu____23195 = FStar_List.tl stack  in
                      norm cfg env1 uu____23195 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____23196);
                       FStar_Syntax_Syntax.pos = uu____23197;
                       FStar_Syntax_Syntax.vars = uu____23198;_},(e,uu____23200)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____23229 when
                    (cfg.steps).primops ->
                    let uu____23244 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____23244 with
                     | (hd1,args) ->
                         let uu____23275 =
                           let uu____23276 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____23276.FStar_Syntax_Syntax.n  in
                         (match uu____23275 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____23280 = find_prim_step cfg fv  in
                              (match uu____23280 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____23283; arity = uu____23284;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____23286;
                                     requires_binder_substitution =
                                       uu____23287;
                                     interpretation = uu____23288;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____23303 -> fallback " (3)" ())
                          | uu____23306 -> fallback " (4)" ()))
                | uu____23307 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____23330  ->
                     let uu____23331 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____23331);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____23340 =
                   log cfg1
                     (fun uu____23345  ->
                        let uu____23346 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____23347 =
                          let uu____23348 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____23375  ->
                                    match uu____23375 with
                                    | (p,uu____23385,uu____23386) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____23348
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____23346 uu____23347);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___93_23403  ->
                                match uu___93_23403 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____23404 -> false))
                         in
                      let steps =
                        let uu___185_23406 = cfg1.steps  in
                        {
                          beta = (uu___185_23406.beta);
                          iota = (uu___185_23406.iota);
                          zeta = false;
                          weak = (uu___185_23406.weak);
                          hnf = (uu___185_23406.hnf);
                          primops = (uu___185_23406.primops);
                          do_not_unfold_pure_lets =
                            (uu___185_23406.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___185_23406.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___185_23406.pure_subterms_within_computations);
                          simplify = (uu___185_23406.simplify);
                          erase_universes = (uu___185_23406.erase_universes);
                          allow_unbound_universes =
                            (uu___185_23406.allow_unbound_universes);
                          reify_ = (uu___185_23406.reify_);
                          compress_uvars = (uu___185_23406.compress_uvars);
                          no_full_norm = (uu___185_23406.no_full_norm);
                          check_no_uvars = (uu___185_23406.check_no_uvars);
                          unmeta = (uu___185_23406.unmeta);
                          unascribe = (uu___185_23406.unascribe);
                          in_full_norm_request =
                            (uu___185_23406.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___185_23406.weakly_reduce_scrutinee)
                        }  in
                      let uu___186_23411 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___186_23411.tcenv);
                        debug = (uu___186_23411.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___186_23411.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___186_23411.memoize_lazy);
                        normalize_pure_lets =
                          (uu___186_23411.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____23483 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____23512 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____23596  ->
                                    fun uu____23597  ->
                                      match (uu____23596, uu____23597) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____23736 = norm_pat env3 p1
                                             in
                                          (match uu____23736 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____23512 with
                           | (pats1,env3) ->
                               ((let uu___187_23898 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___187_23898.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___188_23917 = x  in
                            let uu____23918 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___188_23917.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___188_23917.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23918
                            }  in
                          ((let uu___189_23932 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___189_23932.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___190_23943 = x  in
                            let uu____23944 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___190_23943.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___190_23943.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23944
                            }  in
                          ((let uu___191_23958 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___191_23958.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___192_23974 = x  in
                            let uu____23975 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___192_23974.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___192_23974.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23975
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___193_23990 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___193_23990.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____24006 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____24022 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____24022 with
                                  | (p,wopt,e) ->
                                      let uu____24042 = norm_pat env1 p  in
                                      (match uu____24042 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____24097 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____24097
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____24110 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____24110
                      then
                        norm
                          (let uu___194_24115 = cfg1  in
                           {
                             steps =
                               (let uu___195_24118 = cfg1.steps  in
                                {
                                  beta = (uu___195_24118.beta);
                                  iota = (uu___195_24118.iota);
                                  zeta = (uu___195_24118.zeta);
                                  weak = (uu___195_24118.weak);
                                  hnf = (uu___195_24118.hnf);
                                  primops = (uu___195_24118.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___195_24118.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___195_24118.unfold_until);
                                  unfold_only = (uu___195_24118.unfold_only);
                                  unfold_fully =
                                    (uu___195_24118.unfold_fully);
                                  unfold_attr = (uu___195_24118.unfold_attr);
                                  unfold_tac = (uu___195_24118.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___195_24118.pure_subterms_within_computations);
                                  simplify = (uu___195_24118.simplify);
                                  erase_universes =
                                    (uu___195_24118.erase_universes);
                                  allow_unbound_universes =
                                    (uu___195_24118.allow_unbound_universes);
                                  reify_ = (uu___195_24118.reify_);
                                  compress_uvars =
                                    (uu___195_24118.compress_uvars);
                                  no_full_norm =
                                    (uu___195_24118.no_full_norm);
                                  check_no_uvars =
                                    (uu___195_24118.check_no_uvars);
                                  unmeta = (uu___195_24118.unmeta);
                                  unascribe = (uu___195_24118.unascribe);
                                  in_full_norm_request =
                                    (uu___195_24118.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___194_24115.tcenv);
                             debug = (uu___194_24115.debug);
                             delta_level = (uu___194_24115.delta_level);
                             primitive_steps =
                               (uu___194_24115.primitive_steps);
                             strong = (uu___194_24115.strong);
                             memoize_lazy = (uu___194_24115.memoize_lazy);
                             normalize_pure_lets =
                               (uu___194_24115.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____24120 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____24120)
                    in
                 let rec is_cons head1 =
                   let uu____24145 =
                     let uu____24146 = FStar_Syntax_Subst.compress head1  in
                     uu____24146.FStar_Syntax_Syntax.n  in
                   match uu____24145 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____24150) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____24155 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____24156;
                         FStar_Syntax_Syntax.fv_delta = uu____24157;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____24158;
                         FStar_Syntax_Syntax.fv_delta = uu____24159;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____24160);_}
                       -> true
                   | uu____24167 -> false  in
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
                   let uu____24330 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____24330 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____24411 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____24450 ->
                                 let uu____24451 =
                                   let uu____24452 = is_cons head1  in
                                   Prims.op_Negation uu____24452  in
                                 FStar_Util.Inr uu____24451)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____24477 =
                              let uu____24478 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____24478.FStar_Syntax_Syntax.n  in
                            (match uu____24477 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____24496 ->
                                 let uu____24497 =
                                   let uu____24498 = is_cons head1  in
                                   Prims.op_Negation uu____24498  in
                                 FStar_Util.Inr uu____24497))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____24575)::rest_a,(p1,uu____24578)::rest_p) ->
                       let uu____24622 = matches_pat t2 p1  in
                       (match uu____24622 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____24671 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____24789 = matches_pat scrutinee1 p1  in
                       (match uu____24789 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____24829  ->
                                  let uu____24830 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____24831 =
                                    let uu____24832 =
                                      FStar_List.map
                                        (fun uu____24842  ->
                                           match uu____24842 with
                                           | (uu____24847,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____24832
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____24830 uu____24831);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____24879  ->
                                       match uu____24879 with
                                       | (bv,t2) ->
                                           let uu____24902 =
                                             let uu____24909 =
                                               let uu____24912 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____24912
                                                in
                                             let uu____24913 =
                                               let uu____24914 =
                                                 let uu____24945 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____24945, false)
                                                  in
                                               Clos uu____24914  in
                                             (uu____24909, uu____24913)  in
                                           uu____24902 :: env2) env1 s
                                 in
                              let uu____25058 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____25058)))
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
    let uu____25085 =
      let uu____25088 = FStar_ST.op_Bang plugins  in p :: uu____25088  in
    FStar_ST.op_Colon_Equals plugins uu____25085  in
  let retrieve uu____25196 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____25273  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___94_25314  ->
                  match uu___94_25314 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____25318 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____25324 -> d  in
        let uu____25327 = to_fsteps s  in
        let uu____25328 =
          let uu____25329 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____25330 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____25331 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____25332 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____25333 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____25329;
            primop = uu____25330;
            b380 = uu____25331;
            norm_delayed = uu____25332;
            print_normalized = uu____25333
          }  in
        let uu____25334 =
          let uu____25337 =
            let uu____25340 = retrieve_plugins ()  in
            FStar_List.append uu____25340 psteps  in
          add_steps built_in_primitive_steps uu____25337  in
        let uu____25343 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____25345 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____25345)
           in
        {
          steps = uu____25327;
          tcenv = e;
          debug = uu____25328;
          delta_level = d1;
          primitive_steps = uu____25334;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____25343
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
      fun t  -> let uu____25427 = config s e  in norm_comp uu____25427 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____25444 = config [] env  in norm_universe uu____25444 [] u
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      let cfg =
        config
          [UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          AllowUnboundUniverses;
          EraseUniverses] env
         in
      let non_info t =
        let uu____25468 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25468  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____25475 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___196_25494 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___196_25494.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___196_25494.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____25501 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____25501
          then
            let ct1 =
              let uu____25503 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____25503 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____25510 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____25510
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___197_25514 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___197_25514.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___197_25514.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___197_25514.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___198_25516 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___198_25516.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___198_25516.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___198_25516.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___198_25516.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___199_25517 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___199_25517.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___199_25517.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____25519 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      let cfg =
        config
          [Eager_unfolding;
          UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
          EraseUniverses;
          AllowUnboundUniverses] env
         in
      let non_info t =
        let uu____25537 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25537  in
      let uu____25544 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____25544
      then
        let uu____25545 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____25545 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____25551  ->
                 let uu____25552 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____25552)
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
            ((let uu____25573 =
                let uu____25578 =
                  let uu____25579 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25579
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____25578)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____25573);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____25594 = config [AllowUnboundUniverses] env  in
          norm_comp uu____25594 [] c
        with
        | e ->
            ((let uu____25607 =
                let uu____25612 =
                  let uu____25613 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25613
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____25612)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____25607);
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
                   let uu____25658 =
                     let uu____25659 =
                       let uu____25666 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____25666)  in
                     FStar_Syntax_Syntax.Tm_refine uu____25659  in
                   mk uu____25658 t01.FStar_Syntax_Syntax.pos
               | uu____25671 -> t2)
          | uu____25672 -> t2  in
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
        UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
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
        let uu____25736 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____25736 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____25765 ->
                 let uu____25772 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____25772 with
                  | (actuals,uu____25782,uu____25783) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____25797 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____25797 with
                         | (binders,args) ->
                             let uu____25808 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____25808
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
      | uu____25822 ->
          let uu____25823 = FStar_Syntax_Util.head_and_args t  in
          (match uu____25823 with
           | (head1,args) ->
               let uu____25854 =
                 let uu____25855 = FStar_Syntax_Subst.compress head1  in
                 uu____25855.FStar_Syntax_Syntax.n  in
               (match uu____25854 with
                | FStar_Syntax_Syntax.Tm_uvar u ->
                    let uu____25859 =
                      FStar_Syntax_Util.arrow_formals
                        u.FStar_Syntax_Syntax.ctx_uvar_typ
                       in
                    (match uu____25859 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____25901 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___204_25909 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___204_25909.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___204_25909.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___204_25909.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___204_25909.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___204_25909.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___204_25909.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___204_25909.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___204_25909.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___204_25909.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___204_25909.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___204_25909.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___204_25909.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___204_25909.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___204_25909.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___204_25909.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___204_25909.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___204_25909.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___204_25909.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___204_25909.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___204_25909.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___204_25909.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___204_25909.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___204_25909.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___204_25909.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___204_25909.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___204_25909.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___204_25909.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___204_25909.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___204_25909.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___204_25909.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___204_25909.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___204_25909.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___204_25909.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___204_25909.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___204_25909.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____25901 with
                            | (uu____25910,ty,uu____25912) ->
                                eta_expand_with_type env t ty))
                | uu____25913 ->
                    let uu____25914 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___205_25922 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___205_25922.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___205_25922.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___205_25922.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___205_25922.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___205_25922.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___205_25922.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___205_25922.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___205_25922.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___205_25922.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___205_25922.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___205_25922.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___205_25922.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___205_25922.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___205_25922.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___205_25922.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___205_25922.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___205_25922.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___205_25922.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___205_25922.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___205_25922.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___205_25922.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___205_25922.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___205_25922.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___205_25922.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___205_25922.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___205_25922.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___205_25922.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___205_25922.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___205_25922.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___205_25922.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___205_25922.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___205_25922.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___205_25922.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___205_25922.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___205_25922.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____25914 with
                     | (uu____25923,ty,uu____25925) ->
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
      let uu___206_25998 = x  in
      let uu____25999 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___206_25998.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___206_25998.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____25999
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____26002 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____26027 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____26028 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____26029 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____26030 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____26037 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____26038 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____26039 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___207_26069 = rc  in
          let uu____26070 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____26079 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___207_26069.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____26070;
            FStar_Syntax_Syntax.residual_flags = uu____26079
          }  in
        let uu____26082 =
          let uu____26083 =
            let uu____26100 = elim_delayed_subst_binders bs  in
            let uu____26107 = elim_delayed_subst_term t2  in
            let uu____26110 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____26100, uu____26107, uu____26110)  in
          FStar_Syntax_Syntax.Tm_abs uu____26083  in
        mk1 uu____26082
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____26141 =
          let uu____26142 =
            let uu____26155 = elim_delayed_subst_binders bs  in
            let uu____26162 = elim_delayed_subst_comp c  in
            (uu____26155, uu____26162)  in
          FStar_Syntax_Syntax.Tm_arrow uu____26142  in
        mk1 uu____26141
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____26179 =
          let uu____26180 =
            let uu____26187 = elim_bv bv  in
            let uu____26188 = elim_delayed_subst_term phi  in
            (uu____26187, uu____26188)  in
          FStar_Syntax_Syntax.Tm_refine uu____26180  in
        mk1 uu____26179
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____26215 =
          let uu____26216 =
            let uu____26231 = elim_delayed_subst_term t2  in
            let uu____26234 = elim_delayed_subst_args args  in
            (uu____26231, uu____26234)  in
          FStar_Syntax_Syntax.Tm_app uu____26216  in
        mk1 uu____26215
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___208_26302 = p  in
              let uu____26303 =
                let uu____26304 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____26304  in
              {
                FStar_Syntax_Syntax.v = uu____26303;
                FStar_Syntax_Syntax.p =
                  (uu___208_26302.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___209_26306 = p  in
              let uu____26307 =
                let uu____26308 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____26308  in
              {
                FStar_Syntax_Syntax.v = uu____26307;
                FStar_Syntax_Syntax.p =
                  (uu___209_26306.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___210_26315 = p  in
              let uu____26316 =
                let uu____26317 =
                  let uu____26324 = elim_bv x  in
                  let uu____26325 = elim_delayed_subst_term t0  in
                  (uu____26324, uu____26325)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____26317  in
              {
                FStar_Syntax_Syntax.v = uu____26316;
                FStar_Syntax_Syntax.p =
                  (uu___210_26315.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___211_26348 = p  in
              let uu____26349 =
                let uu____26350 =
                  let uu____26363 =
                    FStar_List.map
                      (fun uu____26386  ->
                         match uu____26386 with
                         | (x,b) ->
                             let uu____26399 = elim_pat x  in
                             (uu____26399, b)) pats
                     in
                  (fv, uu____26363)  in
                FStar_Syntax_Syntax.Pat_cons uu____26350  in
              {
                FStar_Syntax_Syntax.v = uu____26349;
                FStar_Syntax_Syntax.p =
                  (uu___211_26348.FStar_Syntax_Syntax.p)
              }
          | uu____26412 -> p  in
        let elim_branch uu____26436 =
          match uu____26436 with
          | (pat,wopt,t3) ->
              let uu____26462 = elim_pat pat  in
              let uu____26465 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____26468 = elim_delayed_subst_term t3  in
              (uu____26462, uu____26465, uu____26468)
           in
        let uu____26473 =
          let uu____26474 =
            let uu____26497 = elim_delayed_subst_term t2  in
            let uu____26500 = FStar_List.map elim_branch branches  in
            (uu____26497, uu____26500)  in
          FStar_Syntax_Syntax.Tm_match uu____26474  in
        mk1 uu____26473
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____26631 =
          match uu____26631 with
          | (tc,topt) ->
              let uu____26666 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____26676 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____26676
                | FStar_Util.Inr c ->
                    let uu____26678 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____26678
                 in
              let uu____26679 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____26666, uu____26679)
           in
        let uu____26688 =
          let uu____26689 =
            let uu____26716 = elim_delayed_subst_term t2  in
            let uu____26719 = elim_ascription a  in
            (uu____26716, uu____26719, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____26689  in
        mk1 uu____26688
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___212_26780 = lb  in
          let uu____26781 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____26784 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___212_26780.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___212_26780.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____26781;
            FStar_Syntax_Syntax.lbeff =
              (uu___212_26780.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____26784;
            FStar_Syntax_Syntax.lbattrs =
              (uu___212_26780.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___212_26780.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____26787 =
          let uu____26788 =
            let uu____26801 =
              let uu____26808 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____26808)  in
            let uu____26817 = elim_delayed_subst_term t2  in
            (uu____26801, uu____26817)  in
          FStar_Syntax_Syntax.Tm_let uu____26788  in
        mk1 uu____26787
    | FStar_Syntax_Syntax.Tm_uvar u -> mk1 (FStar_Syntax_Syntax.Tm_uvar u)
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____26836 =
          let uu____26837 =
            let uu____26844 = elim_delayed_subst_term tm  in
            (uu____26844, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____26837  in
        mk1 uu____26836
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____26855 =
          let uu____26856 =
            let uu____26863 = elim_delayed_subst_term t2  in
            let uu____26866 = elim_delayed_subst_meta md  in
            (uu____26863, uu____26866)  in
          FStar_Syntax_Syntax.Tm_meta uu____26856  in
        mk1 uu____26855

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___95_26875  ->
         match uu___95_26875 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____26879 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____26879
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
        let uu____26902 =
          let uu____26903 =
            let uu____26912 = elim_delayed_subst_term t  in
            (uu____26912, uopt)  in
          FStar_Syntax_Syntax.Total uu____26903  in
        mk1 uu____26902
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____26929 =
          let uu____26930 =
            let uu____26939 = elim_delayed_subst_term t  in
            (uu____26939, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____26930  in
        mk1 uu____26929
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___213_26948 = ct  in
          let uu____26949 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____26952 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____26961 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___213_26948.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___213_26948.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____26949;
            FStar_Syntax_Syntax.effect_args = uu____26952;
            FStar_Syntax_Syntax.flags = uu____26961
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___96_26964  ->
    match uu___96_26964 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____26976 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____26976
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____27009 =
          let uu____27016 = elim_delayed_subst_term t  in (m, uu____27016)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____27009
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____27028 =
          let uu____27037 = elim_delayed_subst_term t  in
          (m1, m2, uu____27037)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____27028
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____27064  ->
         match uu____27064 with
         | (t,q) ->
             let uu____27075 = elim_delayed_subst_term t  in (uu____27075, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____27095  ->
         match uu____27095 with
         | (x,q) ->
             let uu____27106 =
               let uu___214_27107 = x  in
               let uu____27108 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___214_27107.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___214_27107.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____27108
               }  in
             (uu____27106, q)) bs

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
            | (uu____27200,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____27226,FStar_Util.Inl t) ->
                let uu____27244 =
                  let uu____27251 =
                    let uu____27252 =
                      let uu____27265 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____27265)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____27252  in
                  FStar_Syntax_Syntax.mk uu____27251  in
                uu____27244 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____27279 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____27279 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____27309 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____27372 ->
                    let uu____27373 =
                      let uu____27382 =
                        let uu____27383 = FStar_Syntax_Subst.compress t4  in
                        uu____27383.FStar_Syntax_Syntax.n  in
                      (uu____27382, tc)  in
                    (match uu____27373 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____27410) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____27451) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____27490,FStar_Util.Inl uu____27491) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____27514 -> failwith "Impossible")
                 in
              (match uu____27309 with
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
          let uu____27639 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____27639 with
          | (univ_names1,binders1,tc) ->
              let uu____27705 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____27705)
  
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
          let uu____27754 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____27754 with
          | (univ_names1,binders1,tc) ->
              let uu____27820 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____27820)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____27859 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____27859 with
           | (univ_names1,binders1,typ1) ->
               let uu___215_27893 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___215_27893.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___215_27893.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___215_27893.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___215_27893.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___216_27908 = s  in
          let uu____27909 =
            let uu____27910 =
              let uu____27919 = FStar_List.map (elim_uvars env) sigs  in
              (uu____27919, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____27910  in
          {
            FStar_Syntax_Syntax.sigel = uu____27909;
            FStar_Syntax_Syntax.sigrng =
              (uu___216_27908.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___216_27908.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___216_27908.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___216_27908.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____27936 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27936 with
           | (univ_names1,uu____27956,typ1) ->
               let uu___217_27974 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___217_27974.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___217_27974.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___217_27974.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___217_27974.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____27980 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27980 with
           | (univ_names1,uu____28000,typ1) ->
               let uu___218_28018 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___218_28018.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___218_28018.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___218_28018.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___218_28018.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____28046 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____28046 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____28071 =
                            let uu____28072 =
                              let uu____28073 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____28073  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____28072
                             in
                          elim_delayed_subst_term uu____28071  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___219_28076 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___219_28076.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___219_28076.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___219_28076.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___219_28076.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___220_28077 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___220_28077.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___220_28077.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___220_28077.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___220_28077.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___221_28083 = s  in
          let uu____28084 =
            let uu____28085 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____28085  in
          {
            FStar_Syntax_Syntax.sigel = uu____28084;
            FStar_Syntax_Syntax.sigrng =
              (uu___221_28083.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___221_28083.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___221_28083.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___221_28083.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____28089 = elim_uvars_aux_t env us [] t  in
          (match uu____28089 with
           | (us1,uu____28109,t1) ->
               let uu___222_28127 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___222_28127.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___222_28127.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___222_28127.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___222_28127.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28128 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____28130 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____28130 with
           | (univs1,binders,signature) ->
               let uu____28164 =
                 let uu____28173 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____28173 with
                 | (univs_opening,univs2) ->
                     let uu____28200 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____28200)
                  in
               (match uu____28164 with
                | (univs_opening,univs_closing) ->
                    let uu____28217 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____28223 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____28224 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____28223, uu____28224)  in
                    (match uu____28217 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____28248 =
                           match uu____28248 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____28266 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____28266 with
                                | (us1,t1) ->
                                    let uu____28277 =
                                      let uu____28286 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____28297 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____28286, uu____28297)  in
                                    (match uu____28277 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____28326 =
                                           let uu____28335 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____28346 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____28335, uu____28346)  in
                                         (match uu____28326 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____28376 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____28376
                                                 in
                                              let uu____28377 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____28377 with
                                               | (uu____28400,uu____28401,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____28420 =
                                                       let uu____28421 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____28421
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____28420
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____28430 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____28430 with
                           | (uu____28447,uu____28448,t1) -> t1  in
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
                             | uu____28522 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____28547 =
                               let uu____28548 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____28548.FStar_Syntax_Syntax.n  in
                             match uu____28547 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____28607 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____28638 =
                               let uu____28639 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____28639.FStar_Syntax_Syntax.n  in
                             match uu____28638 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____28660) ->
                                 let uu____28681 = destruct_action_body body
                                    in
                                 (match uu____28681 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____28726 ->
                                 let uu____28727 = destruct_action_body t  in
                                 (match uu____28727 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____28776 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____28776 with
                           | (action_univs,t) ->
                               let uu____28785 = destruct_action_typ_templ t
                                  in
                               (match uu____28785 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___223_28826 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___223_28826.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___223_28826.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___224_28828 = ed  in
                           let uu____28829 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____28830 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____28831 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____28832 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____28833 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____28834 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____28835 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____28836 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____28837 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____28838 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____28839 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____28840 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____28841 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____28842 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___224_28828.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___224_28828.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____28829;
                             FStar_Syntax_Syntax.bind_wp = uu____28830;
                             FStar_Syntax_Syntax.if_then_else = uu____28831;
                             FStar_Syntax_Syntax.ite_wp = uu____28832;
                             FStar_Syntax_Syntax.stronger = uu____28833;
                             FStar_Syntax_Syntax.close_wp = uu____28834;
                             FStar_Syntax_Syntax.assert_p = uu____28835;
                             FStar_Syntax_Syntax.assume_p = uu____28836;
                             FStar_Syntax_Syntax.null_wp = uu____28837;
                             FStar_Syntax_Syntax.trivial = uu____28838;
                             FStar_Syntax_Syntax.repr = uu____28839;
                             FStar_Syntax_Syntax.return_repr = uu____28840;
                             FStar_Syntax_Syntax.bind_repr = uu____28841;
                             FStar_Syntax_Syntax.actions = uu____28842;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___224_28828.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___225_28845 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___225_28845.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___225_28845.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___225_28845.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___225_28845.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___97_28866 =
            match uu___97_28866 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____28897 = elim_uvars_aux_t env us [] t  in
                (match uu____28897 with
                 | (us1,uu____28925,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___226_28952 = sub_eff  in
            let uu____28953 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____28956 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___226_28952.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___226_28952.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____28953;
              FStar_Syntax_Syntax.lift = uu____28956
            }  in
          let uu___227_28959 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___227_28959.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___227_28959.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___227_28959.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___227_28959.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____28969 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____28969 with
           | (univ_names1,binders1,comp1) ->
               let uu___228_29003 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___228_29003.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___228_29003.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___228_29003.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___228_29003.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____29006 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____29007 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  