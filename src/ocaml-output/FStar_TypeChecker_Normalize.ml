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
               let close_one_branch env2 uu____5133 =
                 match uu____5133 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5208 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5229 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5289  ->
                                     fun uu____5290  ->
                                       match (uu____5289, uu____5290) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5381 = norm_pat env4 p1
                                              in
                                           (match uu____5381 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5229 with
                            | (pats1,env4) ->
                                ((let uu___133_5463 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___133_5463.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___134_5482 = x  in
                             let uu____5483 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___134_5482.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___134_5482.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5483
                             }  in
                           ((let uu___135_5489 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___135_5489.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___136_5500 = x  in
                             let uu____5501 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___136_5500.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___136_5500.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5501
                             }  in
                           ((let uu___137_5507 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___137_5507.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___138_5523 = x  in
                             let uu____5524 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___138_5523.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___138_5523.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5524
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___139_5533 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___139_5533.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5538 = norm_pat env2 pat  in
                     (match uu____5538 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____5583 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____5583
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____5602 =
                   let uu____5603 =
                     let uu____5626 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____5626)  in
                   FStar_Syntax_Syntax.Tm_match uu____5603  in
                 mk uu____5602 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____5739 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____5828  ->
                                       match uu____5828 with
                                       | (a,q) ->
                                           let uu____5847 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____5847, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____5739
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____5858 =
                       let uu____5865 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____5865)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____5858
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____5877 =
                       let uu____5886 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____5886)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____5877
                 | uu____5891 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____5897 -> failwith "Impossible: unexpected stack element")

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
        let uu____5911 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____5984  ->
                  fun uu____5985  ->
                    match (uu____5984, uu____5985) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___140_6103 = b  in
                          let uu____6104 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___140_6103.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___140_6103.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6104
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____5911 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6221 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6234 = inline_closure_env cfg env [] t  in
                 let uu____6235 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6234 uu____6235
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6248 = inline_closure_env cfg env [] t  in
                 let uu____6249 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6248 uu____6249
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6293  ->
                           match uu____6293 with
                           | (a,q) ->
                               let uu____6306 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6306, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___84_6321  ->
                           match uu___84_6321 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6325 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6325
                           | f -> f))
                    in
                 let uu____6329 =
                   let uu___141_6330 = c1  in
                   let uu____6331 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6331;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___141_6330.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6329)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___85_6341  ->
            match uu___85_6341 with
            | FStar_Syntax_Syntax.DECREASES uu____6342 -> false
            | uu____6345 -> true))

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
                   (fun uu___86_6363  ->
                      match uu___86_6363 with
                      | FStar_Syntax_Syntax.DECREASES uu____6364 -> false
                      | uu____6367 -> true))
               in
            let rc1 =
              let uu___142_6369 = rc  in
              let uu____6370 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___142_6369.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6370;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6379 -> lopt

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
    let uu____6484 =
      let uu____6493 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6493  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6484  in
  let arg_as_bounded_int uu____6519 =
    match uu____6519 with
    | (a,uu____6531) ->
        let uu____6538 =
          let uu____6539 = FStar_Syntax_Subst.compress a  in
          uu____6539.FStar_Syntax_Syntax.n  in
        (match uu____6538 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6549;
                FStar_Syntax_Syntax.vars = uu____6550;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6552;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6553;_},uu____6554)::[])
             when
             let uu____6593 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6593 "int_to_t" ->
             let uu____6594 =
               let uu____6599 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6599)  in
             FStar_Pervasives_Native.Some uu____6594
         | uu____6604 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6652 = f a  in FStar_Pervasives_Native.Some uu____6652
    | uu____6653 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____6709 = f a0 a1  in FStar_Pervasives_Native.Some uu____6709
    | uu____6710 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____6768 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____6768  in
  let binary_op as_a f res args =
    let uu____6839 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____6839  in
  let as_primitive_step is_strong uu____6876 =
    match uu____6876 with
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
           let uu____6936 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____6936)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____6972 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____6972)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____7001 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____7001)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7037 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7037)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7073 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7073)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7205 =
          let uu____7214 = as_a a  in
          let uu____7217 = as_b b  in (uu____7214, uu____7217)  in
        (match uu____7205 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7232 =
               let uu____7233 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7233  in
             FStar_Pervasives_Native.Some uu____7232
         | uu____7234 -> FStar_Pervasives_Native.None)
    | uu____7243 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7263 =
        let uu____7264 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7264  in
      mk uu____7263 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7276 =
      let uu____7279 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7279  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7276  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7321 =
      let uu____7322 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7322  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7321
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7344 = arg_as_string a1  in
        (match uu____7344 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7350 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7350 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7363 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7363
              | uu____7364 -> FStar_Pervasives_Native.None)
         | uu____7369 -> FStar_Pervasives_Native.None)
    | uu____7372 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7386 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7386
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7423 =
          let uu____7444 = arg_as_string fn  in
          let uu____7447 = arg_as_int from_line  in
          let uu____7450 = arg_as_int from_col  in
          let uu____7453 = arg_as_int to_line  in
          let uu____7456 = arg_as_int to_col  in
          (uu____7444, uu____7447, uu____7450, uu____7453, uu____7456)  in
        (match uu____7423 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7487 =
                 let uu____7488 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7489 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7488 uu____7489  in
               let uu____7490 =
                 let uu____7491 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7492 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7491 uu____7492  in
               FStar_Range.mk_range fn1 uu____7487 uu____7490  in
             let uu____7493 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7493
         | uu____7494 -> FStar_Pervasives_Native.None)
    | uu____7515 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____7548)::(a1,uu____7550)::(a2,uu____7552)::[] ->
        let uu____7589 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7589 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____7594 -> FStar_Pervasives_Native.None)
    | uu____7595 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____7626)::[] ->
        let uu____7635 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____7635 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7641 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7641
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7642 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____7668 =
      let uu____7685 =
        let uu____7702 =
          let uu____7719 =
            let uu____7736 =
              let uu____7753 =
                let uu____7770 =
                  let uu____7787 =
                    let uu____7804 =
                      let uu____7821 =
                        let uu____7838 =
                          let uu____7855 =
                            let uu____7872 =
                              let uu____7889 =
                                let uu____7906 =
                                  let uu____7923 =
                                    let uu____7940 =
                                      let uu____7957 =
                                        let uu____7974 =
                                          let uu____7991 =
                                            let uu____8008 =
                                              let uu____8025 =
                                                let uu____8040 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8040,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8049 =
                                                let uu____8066 =
                                                  let uu____8081 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8081,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8094 =
                                                  let uu____8111 =
                                                    let uu____8126 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8126,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8137 =
                                                    let uu____8154 =
                                                      let uu____8169 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8169,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8154]  in
                                                  uu____8111 :: uu____8137
                                                   in
                                                uu____8066 :: uu____8094  in
                                              uu____8025 :: uu____8049  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8008
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____7991
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____7974
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____7957
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____7940
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8391 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8391 y)))
                                    :: uu____7923
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____7906
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____7889
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____7872
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____7855
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____7838
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____7821
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____8586 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____8586)))
                      :: uu____7804
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____8616 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____8616)))
                    :: uu____7787
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____8646 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____8646)))
                  :: uu____7770
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____8676 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____8676)))
                :: uu____7753
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____7736
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____7719
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____7702
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____7685
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____7668
     in
  let weak_ops =
    let uu____8831 =
      let uu____8846 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____8846, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____8831]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____8926 =
        let uu____8931 =
          let uu____8932 = FStar_Syntax_Syntax.as_arg c  in [uu____8932]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____8931  in
      uu____8926 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9006 =
                let uu____9021 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9021, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9043  ->
                          fun uu____9044  ->
                            match (uu____9043, uu____9044) with
                            | ((int_to_t1,x),(uu____9063,y)) ->
                                let uu____9073 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9073)))
                 in
              let uu____9074 =
                let uu____9091 =
                  let uu____9106 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9106, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9128  ->
                            fun uu____9129  ->
                              match (uu____9128, uu____9129) with
                              | ((int_to_t1,x),(uu____9148,y)) ->
                                  let uu____9158 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9158)))
                   in
                let uu____9159 =
                  let uu____9176 =
                    let uu____9191 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9191, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9213  ->
                              fun uu____9214  ->
                                match (uu____9213, uu____9214) with
                                | ((int_to_t1,x),(uu____9233,y)) ->
                                    let uu____9243 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9243)))
                     in
                  let uu____9244 =
                    let uu____9261 =
                      let uu____9276 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9276, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9294  ->
                                match uu____9294 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9261]  in
                  uu____9176 :: uu____9244  in
                uu____9091 :: uu____9159  in
              uu____9006 :: uu____9074))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9424 =
                let uu____9439 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9439, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9461  ->
                          fun uu____9462  ->
                            match (uu____9461, uu____9462) with
                            | ((int_to_t1,x),(uu____9481,y)) ->
                                let uu____9491 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9491)))
                 in
              let uu____9492 =
                let uu____9509 =
                  let uu____9524 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9524, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9546  ->
                            fun uu____9547  ->
                              match (uu____9546, uu____9547) with
                              | ((int_to_t1,x),(uu____9566,y)) ->
                                  let uu____9576 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9576)))
                   in
                [uu____9509]  in
              uu____9424 :: uu____9492))
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
    | (_typ,uu____9706)::(a1,uu____9708)::(a2,uu____9710)::[] ->
        let uu____9747 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9747 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___143_9751 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___143_9751.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___143_9751.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___144_9753 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___144_9753.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___144_9753.FStar_Syntax_Syntax.vars)
                })
         | uu____9754 -> FStar_Pervasives_Native.None)
    | (_typ,uu____9756)::uu____9757::(a1,uu____9759)::(a2,uu____9761)::[] ->
        let uu____9810 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9810 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___143_9814 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___143_9814.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___143_9814.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___144_9816 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___144_9816.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___144_9816.FStar_Syntax_Syntax.vars)
                })
         | uu____9817 -> FStar_Pervasives_Native.None)
    | uu____9818 -> failwith "Unexpected number of arguments"  in
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
    let uu____9872 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____9872 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____9924 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9924) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____9986  ->
           fun subst1  ->
             match uu____9986 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10027,uu____10028)) ->
                      let uu____10087 = b  in
                      (match uu____10087 with
                       | (bv,uu____10095) ->
                           let uu____10096 =
                             let uu____10097 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10097  in
                           if uu____10096
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10102 = unembed_binder term1  in
                              match uu____10102 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10109 =
                                      let uu___145_10110 = bv  in
                                      let uu____10111 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___145_10110.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___145_10110.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10111
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10109
                                     in
                                  let b_for_x =
                                    let uu____10115 =
                                      let uu____10122 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10122)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10115  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___87_10136  ->
                                         match uu___87_10136 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10137,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10139;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10140;_})
                                             ->
                                             let uu____10145 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10145
                                         | uu____10146 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10147 -> subst1)) env []
  
let reduce_primops :
  'Auu____10170 'Auu____10171 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10170) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10171 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____10217 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10217 with
             | (head1,args) ->
                 let uu____10254 =
                   let uu____10255 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10255.FStar_Syntax_Syntax.n  in
                 (match uu____10254 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10259 = find_prim_step cfg fv  in
                      (match uu____10259 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10281  ->
                                   let uu____10282 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10283 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10290 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10282 uu____10283 uu____10290);
                              tm)
                           else
                             (let uu____10292 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10292 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10371  ->
                                        let uu____10372 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10372);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10375  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10377 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10377 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10383  ->
                                              let uu____10384 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10384);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10390  ->
                                              let uu____10391 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10392 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10391 uu____10392);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10393 ->
                           (log_primops cfg
                              (fun uu____10397  ->
                                 let uu____10398 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10398);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10402  ->
                            let uu____10403 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10403);
                       (match args with
                        | (a1,uu____10405)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10422 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10434  ->
                            let uu____10435 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10435);
                       (match args with
                        | (t,uu____10437)::(r,uu____10439)::[] ->
                            let uu____10466 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____10466 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___146_10470 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___146_10470.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___146_10470.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____10473 -> tm))
                  | uu____10482 -> tm))
  
let reduce_equality :
  'Auu____10493 'Auu____10494 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10493) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10494 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___147_10538 = cfg  in
         {
           steps =
             (let uu___148_10541 = default_steps  in
              {
                beta = (uu___148_10541.beta);
                iota = (uu___148_10541.iota);
                zeta = (uu___148_10541.zeta);
                weak = (uu___148_10541.weak);
                hnf = (uu___148_10541.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___148_10541.do_not_unfold_pure_lets);
                unfold_until = (uu___148_10541.unfold_until);
                unfold_only = (uu___148_10541.unfold_only);
                unfold_fully = (uu___148_10541.unfold_fully);
                unfold_attr = (uu___148_10541.unfold_attr);
                unfold_tac = (uu___148_10541.unfold_tac);
                pure_subterms_within_computations =
                  (uu___148_10541.pure_subterms_within_computations);
                simplify = (uu___148_10541.simplify);
                erase_universes = (uu___148_10541.erase_universes);
                allow_unbound_universes =
                  (uu___148_10541.allow_unbound_universes);
                reify_ = (uu___148_10541.reify_);
                compress_uvars = (uu___148_10541.compress_uvars);
                no_full_norm = (uu___148_10541.no_full_norm);
                check_no_uvars = (uu___148_10541.check_no_uvars);
                unmeta = (uu___148_10541.unmeta);
                unascribe = (uu___148_10541.unascribe);
                in_full_norm_request = (uu___148_10541.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___148_10541.weakly_reduce_scrutinee)
              });
           tcenv = (uu___147_10538.tcenv);
           debug = (uu___147_10538.debug);
           delta_level = (uu___147_10538.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___147_10538.strong);
           memoize_lazy = (uu___147_10538.memoize_lazy);
           normalize_pure_lets = (uu___147_10538.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____10548 .
    FStar_Syntax_Syntax.term -> 'Auu____10548 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10563 =
        let uu____10570 =
          let uu____10571 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10571.FStar_Syntax_Syntax.n  in
        (uu____10570, args)  in
      match uu____10563 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10577::uu____10578::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10582::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10587::uu____10588::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10591 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___88_10604  ->
    match uu___88_10604 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10610 =
          let uu____10613 =
            let uu____10614 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____10614  in
          [uu____10613]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10610
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____10620 =
          let uu____10623 =
            let uu____10624 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____10624  in
          [uu____10623]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10620
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____10645 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10645) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10691 =
          let uu____10696 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____10696 s  in
        match uu____10691 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____10712 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____10712
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____10729::(tm,uu____10731)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____10760)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____10781)::uu____10782::(tm,uu____10784)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____10825 =
            let uu____10830 = full_norm steps  in parse_steps uu____10830  in
          (match uu____10825 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____10869 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___89_10888  ->
    match uu___89_10888 with
    | (App
        (uu____10891,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10892;
                       FStar_Syntax_Syntax.vars = uu____10893;_},uu____10894,uu____10895))::uu____10896
        -> true
    | uu____10901 -> false
  
let firstn :
  'Auu____10910 .
    Prims.int ->
      'Auu____10910 Prims.list ->
        ('Auu____10910 Prims.list,'Auu____10910 Prims.list)
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
          (uu____10952,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10953;
                         FStar_Syntax_Syntax.vars = uu____10954;_},uu____10955,uu____10956))::uu____10957
          -> (cfg.steps).reify_
      | uu____10962 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____10985) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____10995) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11014  ->
                  match uu____11014 with
                  | (a,uu____11022) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11028 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11053 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11054 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11055 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11056 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11057 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11058 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11059 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11060 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11067 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11074 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11087 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11104 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11117 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11124 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11186  ->
                   match uu____11186 with
                   | (a,uu____11194) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11201) ->
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
                     (fun uu____11323  ->
                        match uu____11323 with
                        | (a,uu____11331) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11336,uu____11337,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11343,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11349 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11356 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11357 -> false))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____11649 ->
                   let uu____11674 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____11674
               | uu____11675 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____11683  ->
               let uu____11684 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____11685 = FStar_Syntax_Print.term_to_string t1  in
               let uu____11686 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____11693 =
                 let uu____11694 =
                   let uu____11697 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11697
                    in
                 stack_to_string uu____11694  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11684 uu____11685 uu____11686 uu____11693);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11720 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11721 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____11722 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11723;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11724;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11727;
                 FStar_Syntax_Syntax.fv_delta = uu____11728;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11729;
                 FStar_Syntax_Syntax.fv_delta = uu____11730;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11731);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____11738 ->
               let uu____11745 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____11745
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____11775 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____11775)
               ->
               let cfg' =
                 let uu___149_11777 = cfg  in
                 {
                   steps =
                     (let uu___150_11780 = cfg.steps  in
                      {
                        beta = (uu___150_11780.beta);
                        iota = (uu___150_11780.iota);
                        zeta = (uu___150_11780.zeta);
                        weak = (uu___150_11780.weak);
                        hnf = (uu___150_11780.hnf);
                        primops = (uu___150_11780.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___150_11780.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___150_11780.unfold_attr);
                        unfold_tac = (uu___150_11780.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___150_11780.pure_subterms_within_computations);
                        simplify = (uu___150_11780.simplify);
                        erase_universes = (uu___150_11780.erase_universes);
                        allow_unbound_universes =
                          (uu___150_11780.allow_unbound_universes);
                        reify_ = (uu___150_11780.reify_);
                        compress_uvars = (uu___150_11780.compress_uvars);
                        no_full_norm = (uu___150_11780.no_full_norm);
                        check_no_uvars = (uu___150_11780.check_no_uvars);
                        unmeta = (uu___150_11780.unmeta);
                        unascribe = (uu___150_11780.unascribe);
                        in_full_norm_request =
                          (uu___150_11780.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___150_11780.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___149_11777.tcenv);
                   debug = (uu___149_11777.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___149_11777.primitive_steps);
                   strong = (uu___149_11777.strong);
                   memoize_lazy = (uu___149_11777.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____11785 = get_norm_request (norm cfg' env []) args  in
               (match uu____11785 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____11814  ->
                              fun stack1  ->
                                match uu____11814 with
                                | (a,aq) ->
                                    let uu____11826 =
                                      let uu____11827 =
                                        let uu____11834 =
                                          let uu____11835 =
                                            let uu____11866 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____11866, false)  in
                                          Clos uu____11835  in
                                        (uu____11834, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11827  in
                                    uu____11826 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____11954  ->
                          let uu____11955 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____11955);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____11977 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___90_11982  ->
                                match uu___90_11982 with
                                | UnfoldUntil uu____11983 -> true
                                | UnfoldOnly uu____11984 -> true
                                | UnfoldFully uu____11987 -> true
                                | uu____11990 -> false))
                         in
                      if uu____11977
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___151_11995 = cfg  in
                      let uu____11996 =
                        let uu___152_11997 = to_fsteps s  in
                        {
                          beta = (uu___152_11997.beta);
                          iota = (uu___152_11997.iota);
                          zeta = (uu___152_11997.zeta);
                          weak = (uu___152_11997.weak);
                          hnf = (uu___152_11997.hnf);
                          primops = (uu___152_11997.primops);
                          do_not_unfold_pure_lets =
                            (uu___152_11997.do_not_unfold_pure_lets);
                          unfold_until = (uu___152_11997.unfold_until);
                          unfold_only = (uu___152_11997.unfold_only);
                          unfold_fully = (uu___152_11997.unfold_fully);
                          unfold_attr = (uu___152_11997.unfold_attr);
                          unfold_tac = (uu___152_11997.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___152_11997.pure_subterms_within_computations);
                          simplify = (uu___152_11997.simplify);
                          erase_universes = (uu___152_11997.erase_universes);
                          allow_unbound_universes =
                            (uu___152_11997.allow_unbound_universes);
                          reify_ = (uu___152_11997.reify_);
                          compress_uvars = (uu___152_11997.compress_uvars);
                          no_full_norm = (uu___152_11997.no_full_norm);
                          check_no_uvars = (uu___152_11997.check_no_uvars);
                          unmeta = (uu___152_11997.unmeta);
                          unascribe = (uu___152_11997.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___152_11997.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____11996;
                        tcenv = (uu___151_11995.tcenv);
                        debug = (uu___151_11995.debug);
                        delta_level;
                        primitive_steps = (uu___151_11995.primitive_steps);
                        strong = (uu___151_11995.strong);
                        memoize_lazy = (uu___151_11995.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12006 =
                          let uu____12007 =
                            let uu____12012 = FStar_Util.now ()  in
                            (t1, uu____12012)  in
                          Debug uu____12007  in
                        uu____12006 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12016 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12016
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12025 =
                      let uu____12032 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12032, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12025  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12042 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12042  in
               let uu____12043 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____12043
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____12049  ->
                       let uu____12050 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12051 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12050 uu____12051);
                  if b
                  then
                    (let uu____12052 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____12052 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____12060 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____12060) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____12073),uu____12074);
                                FStar_Syntax_Syntax.sigrng = uu____12075;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____12077;
                                FStar_Syntax_Syntax.sigattrs = uu____12078;_},uu____12079),uu____12080)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____12139 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___91_12143  ->
                               match uu___91_12143 with
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
                          (let uu____12153 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____12153))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____12172) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____12207,uu____12208) -> false)))
                     in
                  let uu____12225 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____12241 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____12241 then (true, true) else (false, false)
                     in
                  match uu____12225 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____12254  ->
                            let uu____12255 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____12256 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____12257 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____12255 uu____12256 uu____12257);
                       if should_delta2
                       then
                         (let uu____12258 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___153_12274 = cfg  in
                                 {
                                   steps =
                                     (let uu___154_12277 = cfg.steps  in
                                      {
                                        beta = (uu___154_12277.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___154_12277.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.Delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___154_12277.unfold_attr);
                                        unfold_tac =
                                          (uu___154_12277.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___154_12277.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___154_12277.erase_universes);
                                        allow_unbound_universes =
                                          (uu___154_12277.allow_unbound_universes);
                                        reify_ = (uu___154_12277.reify_);
                                        compress_uvars =
                                          (uu___154_12277.compress_uvars);
                                        no_full_norm =
                                          (uu___154_12277.no_full_norm);
                                        check_no_uvars =
                                          (uu___154_12277.check_no_uvars);
                                        unmeta = (uu___154_12277.unmeta);
                                        unascribe =
                                          (uu___154_12277.unascribe);
                                        in_full_norm_request =
                                          (uu___154_12277.in_full_norm_request);
                                        weakly_reduce_scrutinee =
                                          (uu___154_12277.weakly_reduce_scrutinee)
                                      });
                                   tcenv = (uu___153_12274.tcenv);
                                   debug = (uu___153_12274.debug);
                                   delta_level = (uu___153_12274.delta_level);
                                   primitive_steps =
                                     (uu___153_12274.primitive_steps);
                                   strong = (uu___153_12274.strong);
                                   memoize_lazy =
                                     (uu___153_12274.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___153_12274.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____12258 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12291 = lookup_bvar env x  in
               (match uu____12291 with
                | Univ uu____12292 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12341 = FStar_ST.op_Bang r  in
                      (match uu____12341 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12463  ->
                                 let uu____12464 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12465 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12464
                                   uu____12465);
                            (let uu____12466 = maybe_weakly_reduced t'  in
                             if uu____12466
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____12467 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12538)::uu____12539 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12548)::uu____12549 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12561,uu____12562))::stack_rest ->
                    (match c with
                     | Univ uu____12566 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12575 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12596  ->
                                    let uu____12597 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12597);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12633  ->
                                    let uu____12634 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12634);
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
                       (fun uu____12708  ->
                          let uu____12709 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12709);
                     norm cfg env stack1 t1)
                | (Debug uu____12710)::uu____12711 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___155_12721 = cfg.steps  in
                             {
                               beta = (uu___155_12721.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_12721.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_12721.unfold_until);
                               unfold_only = (uu___155_12721.unfold_only);
                               unfold_fully = (uu___155_12721.unfold_fully);
                               unfold_attr = (uu___155_12721.unfold_attr);
                               unfold_tac = (uu___155_12721.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_12721.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_12721.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_12721.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_12721.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_12721.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_12721.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_12723 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_12723.tcenv);
                               debug = (uu___156_12723.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_12723.primitive_steps);
                               strong = (uu___156_12723.strong);
                               memoize_lazy = (uu___156_12723.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_12723.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12725 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12725 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12757  -> dummy :: env1) env)
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
                                          let uu____12798 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12798)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_12803 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_12803.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_12803.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12804 -> lopt  in
                           (log cfg
                              (fun uu____12810  ->
                                 let uu____12811 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12811);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_12820 = cfg  in
                               {
                                 steps = (uu___158_12820.steps);
                                 tcenv = (uu___158_12820.tcenv);
                                 debug = (uu___158_12820.debug);
                                 delta_level = (uu___158_12820.delta_level);
                                 primitive_steps =
                                   (uu___158_12820.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_12820.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_12820.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12823)::uu____12824 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___155_12836 = cfg.steps  in
                             {
                               beta = (uu___155_12836.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_12836.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_12836.unfold_until);
                               unfold_only = (uu___155_12836.unfold_only);
                               unfold_fully = (uu___155_12836.unfold_fully);
                               unfold_attr = (uu___155_12836.unfold_attr);
                               unfold_tac = (uu___155_12836.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_12836.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_12836.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_12836.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_12836.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_12836.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_12836.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_12838 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_12838.tcenv);
                               debug = (uu___156_12838.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_12838.primitive_steps);
                               strong = (uu___156_12838.strong);
                               memoize_lazy = (uu___156_12838.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_12838.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12840 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12840 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12872  -> dummy :: env1) env)
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
                                          let uu____12913 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12913)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_12918 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_12918.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_12918.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12919 -> lopt  in
                           (log cfg
                              (fun uu____12925  ->
                                 let uu____12926 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12926);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_12935 = cfg  in
                               {
                                 steps = (uu___158_12935.steps);
                                 tcenv = (uu___158_12935.tcenv);
                                 debug = (uu___158_12935.debug);
                                 delta_level = (uu___158_12935.delta_level);
                                 primitive_steps =
                                   (uu___158_12935.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_12935.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_12935.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____12938)::uu____12939 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___155_12953 = cfg.steps  in
                             {
                               beta = (uu___155_12953.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_12953.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_12953.unfold_until);
                               unfold_only = (uu___155_12953.unfold_only);
                               unfold_fully = (uu___155_12953.unfold_fully);
                               unfold_attr = (uu___155_12953.unfold_attr);
                               unfold_tac = (uu___155_12953.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_12953.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_12953.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_12953.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_12953.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_12953.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_12953.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_12955 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_12955.tcenv);
                               debug = (uu___156_12955.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_12955.primitive_steps);
                               strong = (uu___156_12955.strong);
                               memoize_lazy = (uu___156_12955.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_12955.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12957 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12957 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12989  -> dummy :: env1) env)
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
                                          let uu____13030 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13030)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_13035 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_13035.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_13035.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13036 -> lopt  in
                           (log cfg
                              (fun uu____13042  ->
                                 let uu____13043 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13043);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_13052 = cfg  in
                               {
                                 steps = (uu___158_13052.steps);
                                 tcenv = (uu___158_13052.tcenv);
                                 debug = (uu___158_13052.debug);
                                 delta_level = (uu___158_13052.delta_level);
                                 primitive_steps =
                                   (uu___158_13052.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_13052.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_13052.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13055)::uu____13056 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___155_13070 = cfg.steps  in
                             {
                               beta = (uu___155_13070.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_13070.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_13070.unfold_until);
                               unfold_only = (uu___155_13070.unfold_only);
                               unfold_fully = (uu___155_13070.unfold_fully);
                               unfold_attr = (uu___155_13070.unfold_attr);
                               unfold_tac = (uu___155_13070.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_13070.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_13070.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_13070.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_13070.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_13070.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_13070.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_13072 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_13072.tcenv);
                               debug = (uu___156_13072.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_13072.primitive_steps);
                               strong = (uu___156_13072.strong);
                               memoize_lazy = (uu___156_13072.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_13072.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13074 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13074 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13106  -> dummy :: env1) env)
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
                                          let uu____13147 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13147)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_13152 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_13152.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_13152.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13153 -> lopt  in
                           (log cfg
                              (fun uu____13159  ->
                                 let uu____13160 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13160);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_13169 = cfg  in
                               {
                                 steps = (uu___158_13169.steps);
                                 tcenv = (uu___158_13169.tcenv);
                                 debug = (uu___158_13169.debug);
                                 delta_level = (uu___158_13169.delta_level);
                                 primitive_steps =
                                   (uu___158_13169.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_13169.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_13169.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13172)::uu____13173 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___155_13191 = cfg.steps  in
                             {
                               beta = (uu___155_13191.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_13191.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_13191.unfold_until);
                               unfold_only = (uu___155_13191.unfold_only);
                               unfold_fully = (uu___155_13191.unfold_fully);
                               unfold_attr = (uu___155_13191.unfold_attr);
                               unfold_tac = (uu___155_13191.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_13191.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_13191.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_13191.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_13191.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_13191.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_13191.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_13193 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_13193.tcenv);
                               debug = (uu___156_13193.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_13193.primitive_steps);
                               strong = (uu___156_13193.strong);
                               memoize_lazy = (uu___156_13193.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_13193.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13195 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13195 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13227  -> dummy :: env1) env)
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
                                          let uu____13268 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13268)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_13273 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_13273.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_13273.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13274 -> lopt  in
                           (log cfg
                              (fun uu____13280  ->
                                 let uu____13281 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13281);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_13290 = cfg  in
                               {
                                 steps = (uu___158_13290.steps);
                                 tcenv = (uu___158_13290.tcenv);
                                 debug = (uu___158_13290.debug);
                                 delta_level = (uu___158_13290.delta_level);
                                 primitive_steps =
                                   (uu___158_13290.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_13290.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_13290.normalize_pure_lets)
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
                             let uu___155_13296 = cfg.steps  in
                             {
                               beta = (uu___155_13296.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___155_13296.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___155_13296.unfold_until);
                               unfold_only = (uu___155_13296.unfold_only);
                               unfold_fully = (uu___155_13296.unfold_fully);
                               unfold_attr = (uu___155_13296.unfold_attr);
                               unfold_tac = (uu___155_13296.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___155_13296.erase_universes);
                               allow_unbound_universes =
                                 (uu___155_13296.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___155_13296.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___155_13296.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___155_13296.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___155_13296.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___156_13298 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___156_13298.tcenv);
                               debug = (uu___156_13298.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___156_13298.primitive_steps);
                               strong = (uu___156_13298.strong);
                               memoize_lazy = (uu___156_13298.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___156_13298.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13300 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13300 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13332  -> dummy :: env1) env)
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
                                          let uu____13373 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13373)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___157_13378 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___157_13378.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___157_13378.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13379 -> lopt  in
                           (log cfg
                              (fun uu____13385  ->
                                 let uu____13386 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13386);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___158_13395 = cfg  in
                               {
                                 steps = (uu___158_13395.steps);
                                 tcenv = (uu___158_13395.tcenv);
                                 debug = (uu___158_13395.debug);
                                 delta_level = (uu___158_13395.delta_level);
                                 primitive_steps =
                                   (uu___158_13395.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___158_13395.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___158_13395.normalize_pure_lets)
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
                      (fun uu____13434  ->
                         fun stack1  ->
                           match uu____13434 with
                           | (a,aq) ->
                               let uu____13446 =
                                 let uu____13447 =
                                   let uu____13454 =
                                     let uu____13455 =
                                       let uu____13486 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____13486, false)  in
                                     Clos uu____13455  in
                                   (uu____13454, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____13447  in
                               uu____13446 :: stack1) args)
                  in
               (log cfg
                  (fun uu____13574  ->
                     let uu____13575 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13575);
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
                             ((let uu___159_13621 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___159_13621.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___159_13621.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____13622 ->
                      let uu____13637 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13637)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____13640 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____13640 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____13667 =
                          let uu____13668 =
                            let uu____13675 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___160_13681 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___160_13681.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___160_13681.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13675)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____13668  in
                        mk uu____13667 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____13700 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____13700
               else
                 (let uu____13702 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____13702 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13710 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13732  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____13710 c1  in
                      let t2 =
                        let uu____13754 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____13754 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13865)::uu____13866 ->
                    (log cfg
                       (fun uu____13879  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____13880)::uu____13881 ->
                    (log cfg
                       (fun uu____13892  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____13893,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____13894;
                                   FStar_Syntax_Syntax.vars = uu____13895;_},uu____13896,uu____13897))::uu____13898
                    ->
                    (log cfg
                       (fun uu____13905  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____13906)::uu____13907 ->
                    (log cfg
                       (fun uu____13918  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____13919 ->
                    (log cfg
                       (fun uu____13922  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____13926  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____13943 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____13943
                         | FStar_Util.Inr c ->
                             let uu____13951 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____13951
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____13964 =
                               let uu____13965 =
                                 let uu____13992 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____13992, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____13965
                                in
                             mk uu____13964 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14021 ->
                           let uu____14022 =
                             let uu____14023 =
                               let uu____14024 =
                                 let uu____14051 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14051, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14024
                                in
                             mk uu____14023 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14022))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 if
                   ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee)
                     && (Prims.op_Negation (cfg.steps).weak)
                 then
                   let uu___161_14122 = cfg  in
                   {
                     steps =
                       (let uu___162_14125 = cfg.steps  in
                        {
                          beta = (uu___162_14125.beta);
                          iota = (uu___162_14125.iota);
                          zeta = (uu___162_14125.zeta);
                          weak = true;
                          hnf = (uu___162_14125.hnf);
                          primops = (uu___162_14125.primops);
                          do_not_unfold_pure_lets =
                            (uu___162_14125.do_not_unfold_pure_lets);
                          unfold_until = (uu___162_14125.unfold_until);
                          unfold_only = (uu___162_14125.unfold_only);
                          unfold_fully = (uu___162_14125.unfold_fully);
                          unfold_attr = (uu___162_14125.unfold_attr);
                          unfold_tac = (uu___162_14125.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___162_14125.pure_subterms_within_computations);
                          simplify = (uu___162_14125.simplify);
                          erase_universes = (uu___162_14125.erase_universes);
                          allow_unbound_universes =
                            (uu___162_14125.allow_unbound_universes);
                          reify_ = (uu___162_14125.reify_);
                          compress_uvars = (uu___162_14125.compress_uvars);
                          no_full_norm = (uu___162_14125.no_full_norm);
                          check_no_uvars = (uu___162_14125.check_no_uvars);
                          unmeta = (uu___162_14125.unmeta);
                          unascribe = (uu___162_14125.unascribe);
                          in_full_norm_request =
                            (uu___162_14125.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___162_14125.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___161_14122.tcenv);
                     debug = (uu___161_14122.debug);
                     delta_level = (uu___161_14122.delta_level);
                     primitive_steps = (uu___161_14122.primitive_steps);
                     strong = (uu___161_14122.strong);
                     memoize_lazy = (uu___161_14122.memoize_lazy);
                     normalize_pure_lets =
                       (uu___161_14122.normalize_pure_lets)
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
                         let uu____14161 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14161 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___163_14181 = cfg  in
                               let uu____14182 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___163_14181.steps);
                                 tcenv = uu____14182;
                                 debug = (uu___163_14181.debug);
                                 delta_level = (uu___163_14181.delta_level);
                                 primitive_steps =
                                   (uu___163_14181.primitive_steps);
                                 strong = (uu___163_14181.strong);
                                 memoize_lazy = (uu___163_14181.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___163_14181.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14189 =
                                 let uu____14190 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14190  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14189
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___164_14193 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___164_14193.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___164_14193.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___164_14193.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___164_14193.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____14194 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14194
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14205,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14206;
                               FStar_Syntax_Syntax.lbunivs = uu____14207;
                               FStar_Syntax_Syntax.lbtyp = uu____14208;
                               FStar_Syntax_Syntax.lbeff = uu____14209;
                               FStar_Syntax_Syntax.lbdef = uu____14210;
                               FStar_Syntax_Syntax.lbattrs = uu____14211;
                               FStar_Syntax_Syntax.lbpos = uu____14212;_}::uu____14213),uu____14214)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14254 =
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
               if uu____14254
               then
                 let binder =
                   let uu____14256 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14256  in
                 let env1 =
                   let uu____14266 =
                     let uu____14273 =
                       let uu____14274 =
                         let uu____14305 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14305,
                           false)
                          in
                       Clos uu____14274  in
                     ((FStar_Pervasives_Native.Some binder), uu____14273)  in
                   uu____14266 :: env  in
                 (log cfg
                    (fun uu____14400  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____14404  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14405 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14405))
                 else
                   (let uu____14407 =
                      let uu____14412 =
                        let uu____14413 =
                          let uu____14418 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14418
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14413]  in
                      FStar_Syntax_Subst.open_term uu____14412 body  in
                    match uu____14407 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14439  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14447 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14447  in
                            FStar_Util.Inl
                              (let uu___165_14457 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___165_14457.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___165_14457.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____14460  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___166_14462 = lb  in
                             let uu____14463 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___166_14462.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___166_14462.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14463;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___166_14462.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___166_14462.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14488  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___167_14511 = cfg  in
                             {
                               steps = (uu___167_14511.steps);
                               tcenv = (uu___167_14511.tcenv);
                               debug = (uu___167_14511.debug);
                               delta_level = (uu___167_14511.delta_level);
                               primitive_steps =
                                 (uu___167_14511.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___167_14511.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___167_14511.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____14514  ->
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
               let uu____14531 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____14531 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____14567 =
                               let uu___168_14568 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___168_14568.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___168_14568.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____14567  in
                           let uu____14569 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____14569 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____14595 =
                                   FStar_List.map (fun uu____14611  -> dummy)
                                     lbs1
                                    in
                                 let uu____14612 =
                                   let uu____14621 =
                                     FStar_List.map
                                       (fun uu____14641  -> dummy) xs1
                                      in
                                   FStar_List.append uu____14621 env  in
                                 FStar_List.append uu____14595 uu____14612
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14665 =
                                       let uu___169_14666 = rc  in
                                       let uu____14667 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___169_14666.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14667;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___169_14666.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____14665
                                 | uu____14676 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___170_14682 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___170_14682.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___170_14682.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___170_14682.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___170_14682.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____14692 =
                        FStar_List.map (fun uu____14708  -> dummy) lbs2  in
                      FStar_List.append uu____14692 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____14716 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____14716 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___171_14732 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___171_14732.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___171_14732.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____14761 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____14761
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14780 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14856  ->
                        match uu____14856 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___172_14977 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___172_14977.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___172_14977.FStar_Syntax_Syntax.sort)
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
               (match uu____14780 with
                | (rec_env,memos,uu____15204) ->
                    let uu____15257 =
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
                             let uu____15580 =
                               let uu____15587 =
                                 let uu____15588 =
                                   let uu____15619 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15619, false)
                                    in
                                 Clos uu____15588  in
                               (FStar_Pervasives_Native.None, uu____15587)
                                in
                             uu____15580 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____15723  ->
                     let uu____15724 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15724);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____15746 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____15748::uu____15749 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____15754) ->
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
                             | uu____15777 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____15791 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____15791
                              | uu____15802 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____15808 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____15834 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____15836 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____15837 =
                        let uu____15838 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____15839 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____15838 uu____15839
                         in
                      failwith uu____15837
                    else rebuild cfg env stack t2
                | uu____15841 -> norm cfg env stack t2))

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
                let uu____15851 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____15851  in
              let uu____15852 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____15852 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____15865  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____15876  ->
                        let uu____15877 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____15878 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____15877 uu____15878);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____15883 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____15883 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____15892))::stack1 ->
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
                      | uu____15931 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____15934 ->
                          let uu____15937 =
                            let uu____15938 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____15938
                             in
                          failwith uu____15937
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
                  let uu___173_15962 = cfg  in
                  let uu____15963 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____15963;
                    tcenv = (uu___173_15962.tcenv);
                    debug = (uu___173_15962.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___173_15962.primitive_steps);
                    strong = (uu___173_15962.strong);
                    memoize_lazy = (uu___173_15962.memoize_lazy);
                    normalize_pure_lets =
                      (uu___173_15962.normalize_pure_lets)
                  }
                else
                  (let uu___174_15965 = cfg  in
                   {
                     steps =
                       (let uu___175_15968 = cfg.steps  in
                        {
                          beta = (uu___175_15968.beta);
                          iota = (uu___175_15968.iota);
                          zeta = false;
                          weak = (uu___175_15968.weak);
                          hnf = (uu___175_15968.hnf);
                          primops = (uu___175_15968.primops);
                          do_not_unfold_pure_lets =
                            (uu___175_15968.do_not_unfold_pure_lets);
                          unfold_until = (uu___175_15968.unfold_until);
                          unfold_only = (uu___175_15968.unfold_only);
                          unfold_fully = (uu___175_15968.unfold_fully);
                          unfold_attr = (uu___175_15968.unfold_attr);
                          unfold_tac = (uu___175_15968.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___175_15968.pure_subterms_within_computations);
                          simplify = (uu___175_15968.simplify);
                          erase_universes = (uu___175_15968.erase_universes);
                          allow_unbound_universes =
                            (uu___175_15968.allow_unbound_universes);
                          reify_ = (uu___175_15968.reify_);
                          compress_uvars = (uu___175_15968.compress_uvars);
                          no_full_norm = (uu___175_15968.no_full_norm);
                          check_no_uvars = (uu___175_15968.check_no_uvars);
                          unmeta = (uu___175_15968.unmeta);
                          unascribe = (uu___175_15968.unascribe);
                          in_full_norm_request =
                            (uu___175_15968.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___175_15968.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___174_15965.tcenv);
                     debug = (uu___174_15965.debug);
                     delta_level = (uu___174_15965.delta_level);
                     primitive_steps = (uu___174_15965.primitive_steps);
                     strong = (uu___174_15965.strong);
                     memoize_lazy = (uu___174_15965.memoize_lazy);
                     normalize_pure_lets =
                       (uu___174_15965.normalize_pure_lets)
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
                  (fun uu____16002  ->
                     let uu____16003 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16004 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16003
                       uu____16004);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____16006 =
                   let uu____16007 = FStar_Syntax_Subst.compress head3  in
                   uu____16007.FStar_Syntax_Syntax.n  in
                 match uu____16006 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____16025 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16025
                        in
                     let uu____16026 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16026 with
                      | (uu____16027,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16037 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16047 =
                                   let uu____16048 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16048.FStar_Syntax_Syntax.n  in
                                 match uu____16047 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16054,uu____16055))
                                     ->
                                     let uu____16064 =
                                       let uu____16065 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16065.FStar_Syntax_Syntax.n  in
                                     (match uu____16064 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16071,msrc,uu____16073))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16082 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16082
                                      | uu____16083 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16084 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16085 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16085 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___176_16090 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___176_16090.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___176_16090.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___176_16090.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___176_16090.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___176_16090.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____16091 = FStar_List.tl stack  in
                                    let uu____16092 =
                                      let uu____16093 =
                                        let uu____16100 =
                                          let uu____16101 =
                                            let uu____16114 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16114)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16101
                                           in
                                        FStar_Syntax_Syntax.mk uu____16100
                                         in
                                      uu____16093
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16091 uu____16092
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16130 =
                                      let uu____16131 = is_return body  in
                                      match uu____16131 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16135;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16136;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16139 -> false  in
                                    if uu____16130
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
                                         let uu____16156 =
                                           let uu____16163 =
                                             let uu____16164 =
                                               let uu____16181 =
                                                 let uu____16188 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16188]  in
                                               (uu____16181, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16164
                                              in
                                           FStar_Syntax_Syntax.mk uu____16163
                                            in
                                         uu____16156
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16210 =
                                           let uu____16211 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16211.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16210 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16217::uu____16218::[])
                                             ->
                                             let uu____16223 =
                                               let uu____16230 =
                                                 let uu____16231 =
                                                   let uu____16238 =
                                                     let uu____16239 =
                                                       let uu____16240 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16240
                                                        in
                                                     let uu____16241 =
                                                       let uu____16244 =
                                                         let uu____16245 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16245
                                                          in
                                                       [uu____16244]  in
                                                     uu____16239 ::
                                                       uu____16241
                                                      in
                                                   (bind1, uu____16238)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16231
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16230
                                                in
                                             uu____16223
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16251 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____16257 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____16257
                                         then
                                           let uu____16260 =
                                             let uu____16261 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16261
                                              in
                                           let uu____16262 =
                                             let uu____16265 =
                                               let uu____16266 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____16266
                                                in
                                             [uu____16265]  in
                                           uu____16260 :: uu____16262
                                         else []  in
                                       let reified =
                                         let uu____16271 =
                                           let uu____16278 =
                                             let uu____16279 =
                                               let uu____16294 =
                                                 let uu____16303 =
                                                   let uu____16306 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____16307 =
                                                     let uu____16310 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____16310]  in
                                                   uu____16306 :: uu____16307
                                                    in
                                                 let uu____16311 =
                                                   let uu____16314 =
                                                     let uu____16317 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16318 =
                                                       let uu____16321 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____16322 =
                                                         let uu____16325 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____16326 =
                                                           let uu____16329 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____16329]  in
                                                         uu____16325 ::
                                                           uu____16326
                                                          in
                                                       uu____16321 ::
                                                         uu____16322
                                                        in
                                                     uu____16317 ::
                                                       uu____16318
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____16314
                                                    in
                                                 FStar_List.append
                                                   uu____16303 uu____16311
                                                  in
                                               (bind_inst, uu____16294)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16279
                                              in
                                           FStar_Syntax_Syntax.mk uu____16278
                                            in
                                         uu____16271
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____16347  ->
                                            let uu____16348 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____16349 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____16348 uu____16349);
                                       (let uu____16350 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____16350 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____16374 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16374
                        in
                     let uu____16375 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16375 with
                      | (uu____16376,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____16413 =
                                  let uu____16414 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____16414.FStar_Syntax_Syntax.n  in
                                match uu____16413 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____16418) -> t2
                                | uu____16423 -> head4  in
                              let uu____16424 =
                                let uu____16425 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____16425.FStar_Syntax_Syntax.n  in
                              match uu____16424 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____16431 -> FStar_Pervasives_Native.None
                               in
                            let uu____16432 = maybe_extract_fv head4  in
                            match uu____16432 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____16442 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____16442
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____16447 = maybe_extract_fv head5
                                     in
                                  match uu____16447 with
                                  | FStar_Pervasives_Native.Some uu____16452
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____16453 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____16458 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____16473 =
                              match uu____16473 with
                              | (e,q) ->
                                  let uu____16480 =
                                    let uu____16481 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____16481.FStar_Syntax_Syntax.n  in
                                  (match uu____16480 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____16496 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____16496
                                   | uu____16497 -> false)
                               in
                            let uu____16498 =
                              let uu____16499 =
                                let uu____16508 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____16508 :: args  in
                              FStar_Util.for_some is_arg_impure uu____16499
                               in
                            if uu____16498
                            then
                              let uu____16527 =
                                let uu____16528 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____16528
                                 in
                              failwith uu____16527
                            else ());
                           (let uu____16530 = maybe_unfold_action head_app
                               in
                            match uu____16530 with
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
                                   (fun uu____16573  ->
                                      let uu____16574 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____16575 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____16574 uu____16575);
                                 (let uu____16576 = FStar_List.tl stack  in
                                  norm cfg env uu____16576 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____16578) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____16602 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____16602  in
                     (log cfg
                        (fun uu____16606  ->
                           let uu____16607 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____16607);
                      (let uu____16608 = FStar_List.tl stack  in
                       norm cfg env uu____16608 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____16725  ->
                               match uu____16725 with
                               | (pat,wopt,tm) ->
                                   let uu____16767 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____16767)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____16799 = FStar_List.tl stack  in
                     norm cfg env uu____16799 tm
                 | uu____16800 -> fallback ())

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
              (fun uu____16814  ->
                 let uu____16815 = FStar_Ident.string_of_lid msrc  in
                 let uu____16816 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16817 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16815
                   uu____16816 uu____16817);
            (let uu____16818 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____16818
             then
               let ed =
                 let uu____16820 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____16820  in
               let uu____16821 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____16821 with
               | (uu____16822,return_repr) ->
                   let return_inst =
                     let uu____16835 =
                       let uu____16836 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____16836.FStar_Syntax_Syntax.n  in
                     match uu____16835 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____16842::[]) ->
                         let uu____16847 =
                           let uu____16854 =
                             let uu____16855 =
                               let uu____16862 =
                                 let uu____16863 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____16863]  in
                               (return_tm, uu____16862)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____16855  in
                           FStar_Syntax_Syntax.mk uu____16854  in
                         uu____16847 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____16869 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____16872 =
                     let uu____16879 =
                       let uu____16880 =
                         let uu____16895 =
                           let uu____16904 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____16905 =
                             let uu____16908 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____16908]  in
                           uu____16904 :: uu____16905  in
                         (return_inst, uu____16895)  in
                       FStar_Syntax_Syntax.Tm_app uu____16880  in
                     FStar_Syntax_Syntax.mk uu____16879  in
                   uu____16872 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____16923 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____16923 with
                | FStar_Pervasives_Native.None  ->
                    let uu____16926 =
                      let uu____16927 = FStar_Ident.text_of_lid msrc  in
                      let uu____16928 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____16927 uu____16928
                       in
                    failwith uu____16926
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16929;
                      FStar_TypeChecker_Env.mtarget = uu____16930;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16931;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____16953 =
                      let uu____16954 = FStar_Ident.text_of_lid msrc  in
                      let uu____16955 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____16954 uu____16955
                       in
                    failwith uu____16953
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16956;
                      FStar_TypeChecker_Env.mtarget = uu____16957;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16958;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____16993 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____16994 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____16993 t FStar_Syntax_Syntax.tun uu____16994))

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
                (fun uu____17050  ->
                   match uu____17050 with
                   | (a,imp) ->
                       let uu____17061 = norm cfg env [] a  in
                       (uu____17061, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____17069  ->
             let uu____17070 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17071 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____17070 uu____17071);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17095 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____17095
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___177_17098 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___177_17098.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___177_17098.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17120 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____17120
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___178_17123 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___178_17123.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___178_17123.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17160  ->
                      match uu____17160 with
                      | (a,i) ->
                          let uu____17171 = norm cfg env [] a  in
                          (uu____17171, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___92_17189  ->
                       match uu___92_17189 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17193 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17193
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___179_17201 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___180_17204 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___180_17204.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___179_17201.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___179_17201.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____17207  ->
        match uu____17207 with
        | (x,imp) ->
            let uu____17210 =
              let uu___181_17211 = x  in
              let uu____17212 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___181_17211.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___181_17211.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17212
              }  in
            (uu____17210, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17218 =
          FStar_List.fold_left
            (fun uu____17236  ->
               fun b  ->
                 match uu____17236 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17218 with | (nbs,uu____17268) -> FStar_List.rev nbs

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
            let uu____17284 =
              let uu___182_17285 = rc  in
              let uu____17286 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___182_17285.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17286;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___182_17285.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17284
        | uu____17295 -> lopt

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
            (let uu____17316 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17317 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____17316
               uu____17317)
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
          let uu____17337 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____17337
          then tm1
          else
            (let w t =
               let uu___183_17351 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___183_17351.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___183_17351.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17362 =
                 let uu____17363 = FStar_Syntax_Util.unmeta t  in
                 uu____17363.FStar_Syntax_Syntax.n  in
               match uu____17362 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17370 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17419)::args1,(bv,uu____17422)::bs1) ->
                   let uu____17456 =
                     let uu____17457 = FStar_Syntax_Subst.compress t  in
                     uu____17457.FStar_Syntax_Syntax.n  in
                   (match uu____17456 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17461 -> false)
               | ([],[]) -> true
               | (uu____17482,uu____17483) -> false  in
             let is_applied bs t =
               let uu____17523 = FStar_Syntax_Util.head_and_args' t  in
               match uu____17523 with
               | (hd1,args) ->
                   let uu____17556 =
                     let uu____17557 = FStar_Syntax_Subst.compress hd1  in
                     uu____17557.FStar_Syntax_Syntax.n  in
                   (match uu____17556 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____17563 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____17579 = FStar_Syntax_Util.is_squash t  in
               match uu____17579 with
               | FStar_Pervasives_Native.Some (uu____17590,t') ->
                   is_applied bs t'
               | uu____17602 ->
                   let uu____17611 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____17611 with
                    | FStar_Pervasives_Native.Some (uu____17622,t') ->
                        is_applied bs t'
                    | uu____17634 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____17653 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17653 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____17660)::(q,uu____17662)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____17689 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____17689 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____17694 =
                          let uu____17695 = FStar_Syntax_Subst.compress p  in
                          uu____17695.FStar_Syntax_Syntax.n  in
                        (match uu____17694 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____17701 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____17701
                         | uu____17704 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____17707)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____17724 =
                          let uu____17725 = FStar_Syntax_Subst.compress p1
                             in
                          uu____17725.FStar_Syntax_Syntax.n  in
                        (match uu____17724 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____17731 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____17731
                         | uu____17734 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____17738 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____17738 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____17743 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____17743 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____17752 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____17752
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____17757)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____17774 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____17774 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____17783 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____17783
                              | uu____17786 -> FStar_Pervasives_Native.None)
                         | uu____17789 -> FStar_Pervasives_Native.None)
                    | uu____17792 -> FStar_Pervasives_Native.None)
               | uu____17795 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____17808 =
                 let uu____17809 = FStar_Syntax_Subst.compress phi  in
                 uu____17809.FStar_Syntax_Syntax.n  in
               match uu____17808 with
               | FStar_Syntax_Syntax.Tm_match (uu____17814,br::brs) ->
                   let uu____17881 = br  in
                   (match uu____17881 with
                    | (uu____17898,uu____17899,e) ->
                        let r =
                          let uu____17920 = simp_t e  in
                          match uu____17920 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____17926 =
                                FStar_List.for_all
                                  (fun uu____17944  ->
                                     match uu____17944 with
                                     | (uu____17957,uu____17958,e') ->
                                         let uu____17972 = simp_t e'  in
                                         uu____17972 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____17926
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____17980 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____17989 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____17989
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18014 =
                 match uu____18014 with
                 | (t1,q) ->
                     let uu____18025 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18025 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18051 -> (t1, q))
                  in
               let uu____18060 = FStar_Syntax_Util.head_and_args t  in
               match uu____18060 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18126 =
                 let uu____18127 = FStar_Syntax_Util.unmeta ty  in
                 uu____18127.FStar_Syntax_Syntax.n  in
               match uu____18126 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18131) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18136,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18156 -> false  in
             let simplify1 arg =
               let uu____18181 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18181, arg)  in
             let uu____18190 = is_quantified_const tm1  in
             match uu____18190 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____18194 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____18194
             | FStar_Pervasives_Native.None  ->
                 let uu____18195 =
                   let uu____18196 = FStar_Syntax_Subst.compress tm1  in
                   uu____18196.FStar_Syntax_Syntax.n  in
                 (match uu____18195 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18200;
                              FStar_Syntax_Syntax.vars = uu____18201;_},uu____18202);
                         FStar_Syntax_Syntax.pos = uu____18203;
                         FStar_Syntax_Syntax.vars = uu____18204;_},args)
                      ->
                      let uu____18230 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18230
                      then
                        let uu____18231 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18231 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18276)::
                             (uu____18277,(arg,uu____18279))::[] ->
                             maybe_auto_squash arg
                         | (uu____18328,(arg,uu____18330))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18331)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18380)::uu____18381::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18432::(FStar_Pervasives_Native.Some (false
                                         ),uu____18433)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18484 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18498 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18498
                         then
                           let uu____18499 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18499 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18544)::uu____18545::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18596::(FStar_Pervasives_Native.Some (true
                                           ),uu____18597)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18648)::(uu____18649,(arg,uu____18651))::[]
                               -> maybe_auto_squash arg
                           | (uu____18700,(arg,uu____18702))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18703)::[]
                               -> maybe_auto_squash arg
                           | uu____18752 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18766 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18766
                            then
                              let uu____18767 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18767 with
                              | uu____18812::(FStar_Pervasives_Native.Some
                                              (true ),uu____18813)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18864)::uu____18865::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18916)::(uu____18917,(arg,uu____18919))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18968,(p,uu____18970))::(uu____18971,
                                                                (q,uu____18973))::[]
                                  ->
                                  let uu____19020 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19020
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19022 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19036 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19036
                               then
                                 let uu____19037 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19037 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19082)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19083)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19134)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19135)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19186)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19187)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19238)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19239)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19290,(arg,uu____19292))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19293)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19342)::(uu____19343,(arg,uu____19345))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19394,(arg,uu____19396))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19397)::[]
                                     ->
                                     let uu____19446 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19446
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19447)::(uu____19448,(arg,uu____19450))::[]
                                     ->
                                     let uu____19499 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19499
                                 | (uu____19500,(p,uu____19502))::(uu____19503,
                                                                   (q,uu____19505))::[]
                                     ->
                                     let uu____19552 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19552
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19554 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19568 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19568
                                  then
                                    let uu____19569 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19569 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19614)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19645)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19676 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19690 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19690
                                     then
                                       match args with
                                       | (t,uu____19692)::[] ->
                                           let uu____19709 =
                                             let uu____19710 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19710.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19709 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19713::[],body,uu____19715)
                                                ->
                                                let uu____19742 = simp_t body
                                                   in
                                                (match uu____19742 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19745 -> tm1)
                                            | uu____19748 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19750))::(t,uu____19752)::[]
                                           ->
                                           let uu____19779 =
                                             let uu____19780 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19780.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19779 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19783::[],body,uu____19785)
                                                ->
                                                let uu____19812 = simp_t body
                                                   in
                                                (match uu____19812 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19815 -> tm1)
                                            | uu____19818 -> tm1)
                                       | uu____19819 -> tm1
                                     else
                                       (let uu____19829 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____19829
                                        then
                                          match args with
                                          | (t,uu____19831)::[] ->
                                              let uu____19848 =
                                                let uu____19849 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19849.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19848 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19852::[],body,uu____19854)
                                                   ->
                                                   let uu____19881 =
                                                     simp_t body  in
                                                   (match uu____19881 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____19884 -> tm1)
                                               | uu____19887 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____19889))::(t,uu____19891)::[]
                                              ->
                                              let uu____19918 =
                                                let uu____19919 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19919.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19918 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19922::[],body,uu____19924)
                                                   ->
                                                   let uu____19951 =
                                                     simp_t body  in
                                                   (match uu____19951 with
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
                                                    | uu____19954 -> tm1)
                                               | uu____19957 -> tm1)
                                          | uu____19958 -> tm1
                                        else
                                          (let uu____19968 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____19968
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19969;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19970;_},uu____19971)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19988;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19989;_},uu____19990)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20007 -> tm1
                                           else
                                             (let uu____20017 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20017 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20037 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20047;
                         FStar_Syntax_Syntax.vars = uu____20048;_},args)
                      ->
                      let uu____20070 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20070
                      then
                        let uu____20071 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20071 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20116)::
                             (uu____20117,(arg,uu____20119))::[] ->
                             maybe_auto_squash arg
                         | (uu____20168,(arg,uu____20170))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20171)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20220)::uu____20221::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20272::(FStar_Pervasives_Native.Some (false
                                         ),uu____20273)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20324 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20338 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20338
                         then
                           let uu____20339 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20339 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____20384)::uu____20385::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____20436::(FStar_Pervasives_Native.Some (true
                                           ),uu____20437)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____20488)::(uu____20489,(arg,uu____20491))::[]
                               -> maybe_auto_squash arg
                           | (uu____20540,(arg,uu____20542))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____20543)::[]
                               -> maybe_auto_squash arg
                           | uu____20592 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____20606 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____20606
                            then
                              let uu____20607 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____20607 with
                              | uu____20652::(FStar_Pervasives_Native.Some
                                              (true ),uu____20653)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____20704)::uu____20705::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____20756)::(uu____20757,(arg,uu____20759))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20808,(p,uu____20810))::(uu____20811,
                                                                (q,uu____20813))::[]
                                  ->
                                  let uu____20860 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____20860
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20862 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20876 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20876
                               then
                                 let uu____20877 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____20877 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20922)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20923)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20974)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20975)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21026)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21027)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21078)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21079)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21130,(arg,uu____21132))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21133)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21182)::(uu____21183,(arg,uu____21185))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21234,(arg,uu____21236))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21237)::[]
                                     ->
                                     let uu____21286 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21286
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21287)::(uu____21288,(arg,uu____21290))::[]
                                     ->
                                     let uu____21339 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21339
                                 | (uu____21340,(p,uu____21342))::(uu____21343,
                                                                   (q,uu____21345))::[]
                                     ->
                                     let uu____21392 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21392
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21394 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21408 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____21408
                                  then
                                    let uu____21409 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____21409 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____21454)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21485)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21516 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21530 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21530
                                     then
                                       match args with
                                       | (t,uu____21532)::[] ->
                                           let uu____21549 =
                                             let uu____21550 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21550.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21549 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21553::[],body,uu____21555)
                                                ->
                                                let uu____21582 = simp_t body
                                                   in
                                                (match uu____21582 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21585 -> tm1)
                                            | uu____21588 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21590))::(t,uu____21592)::[]
                                           ->
                                           let uu____21619 =
                                             let uu____21620 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21620.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21619 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21623::[],body,uu____21625)
                                                ->
                                                let uu____21652 = simp_t body
                                                   in
                                                (match uu____21652 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21655 -> tm1)
                                            | uu____21658 -> tm1)
                                       | uu____21659 -> tm1
                                     else
                                       (let uu____21669 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21669
                                        then
                                          match args with
                                          | (t,uu____21671)::[] ->
                                              let uu____21688 =
                                                let uu____21689 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21689.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21688 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21692::[],body,uu____21694)
                                                   ->
                                                   let uu____21721 =
                                                     simp_t body  in
                                                   (match uu____21721 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21724 -> tm1)
                                               | uu____21727 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21729))::(t,uu____21731)::[]
                                              ->
                                              let uu____21758 =
                                                let uu____21759 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21759.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21758 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21762::[],body,uu____21764)
                                                   ->
                                                   let uu____21791 =
                                                     simp_t body  in
                                                   (match uu____21791 with
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
                                                    | uu____21794 -> tm1)
                                               | uu____21797 -> tm1)
                                          | uu____21798 -> tm1
                                        else
                                          (let uu____21808 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____21808
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21809;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21810;_},uu____21811)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21828;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21829;_},uu____21830)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21847 -> tm1
                                           else
                                             (let uu____21857 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____21857 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____21877 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____21892 = simp_t t  in
                      (match uu____21892 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____21895 ->
                      let uu____21918 = is_const_match tm1  in
                      (match uu____21918 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____21921 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____21931  ->
               (let uu____21933 = FStar_Syntax_Print.tag_of_term t  in
                let uu____21934 = FStar_Syntax_Print.term_to_string t  in
                let uu____21935 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____21942 =
                  let uu____21943 =
                    let uu____21946 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____21946
                     in
                  stack_to_string uu____21943  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____21933 uu____21934 uu____21935 uu____21942);
               (let uu____21969 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____21969
                then
                  let uu____21970 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____21970 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____21977 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____21978 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____21979 =
                          let uu____21980 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____21980
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____21977
                          uu____21978 uu____21979);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____21998 =
                     let uu____21999 =
                       let uu____22000 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____22000  in
                     FStar_Util.string_of_int uu____21999  in
                   let uu____22005 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____22006 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____21998 uu____22005 uu____22006)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____22012,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____22063  ->
                     let uu____22064 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____22064);
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
               let uu____22102 =
                 let uu___184_22103 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___184_22103.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___184_22103.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____22102
           | (Arg (Univ uu____22106,uu____22107,uu____22108))::uu____22109 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____22112,uu____22113))::uu____22114 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____22129,uu____22130),aq,r))::stack1
               when
               let uu____22180 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____22180 ->
               let t2 =
                 let uu____22184 =
                   let uu____22189 =
                     let uu____22190 = closure_as_term cfg env_arg tm  in
                     (uu____22190, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____22189  in
                 uu____22184 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____22200),aq,r))::stack1 ->
               (log cfg
                  (fun uu____22253  ->
                     let uu____22254 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____22254);
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
                  (let uu____22266 = FStar_ST.op_Bang m  in
                   match uu____22266 with
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
                   | FStar_Pervasives_Native.Some (uu____22409,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____22462 =
                 log cfg
                   (fun uu____22466  ->
                      let uu____22467 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____22467);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____22473 =
                 let uu____22474 = FStar_Syntax_Subst.compress t1  in
                 uu____22474.FStar_Syntax_Syntax.n  in
               (match uu____22473 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____22501 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____22501  in
                    (log cfg
                       (fun uu____22505  ->
                          let uu____22506 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____22506);
                     (let uu____22507 = FStar_List.tl stack  in
                      norm cfg env1 uu____22507 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____22508);
                       FStar_Syntax_Syntax.pos = uu____22509;
                       FStar_Syntax_Syntax.vars = uu____22510;_},(e,uu____22512)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____22541 when
                    (cfg.steps).primops ->
                    let uu____22556 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____22556 with
                     | (hd1,args) ->
                         let uu____22593 =
                           let uu____22594 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____22594.FStar_Syntax_Syntax.n  in
                         (match uu____22593 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____22598 = find_prim_step cfg fv  in
                              (match uu____22598 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____22601; arity = uu____22602;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____22604;
                                     requires_binder_substitution =
                                       uu____22605;
                                     interpretation = uu____22606;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____22621 -> fallback " (3)" ())
                          | uu____22624 -> fallback " (4)" ()))
                | uu____22625 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____22648  ->
                     let uu____22649 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____22649);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____22658 =
                   log cfg1
                     (fun uu____22663  ->
                        let uu____22664 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____22665 =
                          let uu____22666 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____22693  ->
                                    match uu____22693 with
                                    | (p,uu____22703,uu____22704) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____22666
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____22664 uu____22665);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___93_22721  ->
                                match uu___93_22721 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____22722 -> false))
                         in
                      let steps =
                        let uu___185_22724 = cfg1.steps  in
                        {
                          beta = (uu___185_22724.beta);
                          iota = (uu___185_22724.iota);
                          zeta = false;
                          weak = (uu___185_22724.weak);
                          hnf = (uu___185_22724.hnf);
                          primops = (uu___185_22724.primops);
                          do_not_unfold_pure_lets =
                            (uu___185_22724.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___185_22724.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___185_22724.pure_subterms_within_computations);
                          simplify = (uu___185_22724.simplify);
                          erase_universes = (uu___185_22724.erase_universes);
                          allow_unbound_universes =
                            (uu___185_22724.allow_unbound_universes);
                          reify_ = (uu___185_22724.reify_);
                          compress_uvars = (uu___185_22724.compress_uvars);
                          no_full_norm = (uu___185_22724.no_full_norm);
                          check_no_uvars = (uu___185_22724.check_no_uvars);
                          unmeta = (uu___185_22724.unmeta);
                          unascribe = (uu___185_22724.unascribe);
                          in_full_norm_request =
                            (uu___185_22724.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___185_22724.weakly_reduce_scrutinee)
                        }  in
                      let uu___186_22729 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___186_22729.tcenv);
                        debug = (uu___186_22729.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___186_22729.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___186_22729.memoize_lazy);
                        normalize_pure_lets =
                          (uu___186_22729.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____22769 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____22790 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____22850  ->
                                    fun uu____22851  ->
                                      match (uu____22850, uu____22851) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____22942 = norm_pat env3 p1
                                             in
                                          (match uu____22942 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____22790 with
                           | (pats1,env3) ->
                               ((let uu___187_23024 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___187_23024.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___188_23043 = x  in
                            let uu____23044 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___188_23043.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___188_23043.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23044
                            }  in
                          ((let uu___189_23050 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___189_23050.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___190_23061 = x  in
                            let uu____23062 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___190_23061.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___190_23061.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23062
                            }  in
                          ((let uu___191_23068 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___191_23068.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___192_23084 = x  in
                            let uu____23085 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___192_23084.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___192_23084.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23085
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___193_23092 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___193_23092.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____23108 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____23124 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____23124 with
                                  | (p,wopt,e) ->
                                      let uu____23144 = norm_pat env1 p  in
                                      (match uu____23144 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____23175 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____23175
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____23188 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____23188
                      then
                        norm
                          (let uu___194_23193 = cfg1  in
                           {
                             steps =
                               (let uu___195_23196 = cfg1.steps  in
                                {
                                  beta = (uu___195_23196.beta);
                                  iota = (uu___195_23196.iota);
                                  zeta = (uu___195_23196.zeta);
                                  weak = (uu___195_23196.weak);
                                  hnf = (uu___195_23196.hnf);
                                  primops = (uu___195_23196.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___195_23196.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___195_23196.unfold_until);
                                  unfold_only = (uu___195_23196.unfold_only);
                                  unfold_fully =
                                    (uu___195_23196.unfold_fully);
                                  unfold_attr = (uu___195_23196.unfold_attr);
                                  unfold_tac = (uu___195_23196.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___195_23196.pure_subterms_within_computations);
                                  simplify = (uu___195_23196.simplify);
                                  erase_universes =
                                    (uu___195_23196.erase_universes);
                                  allow_unbound_universes =
                                    (uu___195_23196.allow_unbound_universes);
                                  reify_ = (uu___195_23196.reify_);
                                  compress_uvars =
                                    (uu___195_23196.compress_uvars);
                                  no_full_norm =
                                    (uu___195_23196.no_full_norm);
                                  check_no_uvars =
                                    (uu___195_23196.check_no_uvars);
                                  unmeta = (uu___195_23196.unmeta);
                                  unascribe = (uu___195_23196.unascribe);
                                  in_full_norm_request =
                                    (uu___195_23196.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___194_23193.tcenv);
                             debug = (uu___194_23193.debug);
                             delta_level = (uu___194_23193.delta_level);
                             primitive_steps =
                               (uu___194_23193.primitive_steps);
                             strong = (uu___194_23193.strong);
                             memoize_lazy = (uu___194_23193.memoize_lazy);
                             normalize_pure_lets =
                               (uu___194_23193.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____23198 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____23198)
                    in
                 let rec is_cons head1 =
                   let uu____23223 =
                     let uu____23224 = FStar_Syntax_Subst.compress head1  in
                     uu____23224.FStar_Syntax_Syntax.n  in
                   match uu____23223 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____23228) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____23233 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____23234;
                         FStar_Syntax_Syntax.fv_delta = uu____23235;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____23236;
                         FStar_Syntax_Syntax.fv_delta = uu____23237;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____23238);_}
                       -> true
                   | uu____23245 -> false  in
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
                   let uu____23408 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____23408 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____23495 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____23534 ->
                                 let uu____23535 =
                                   let uu____23536 = is_cons head1  in
                                   Prims.op_Negation uu____23536  in
                                 FStar_Util.Inr uu____23535)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____23561 =
                              let uu____23562 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____23562.FStar_Syntax_Syntax.n  in
                            (match uu____23561 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____23580 ->
                                 let uu____23581 =
                                   let uu____23582 = is_cons head1  in
                                   Prims.op_Negation uu____23582  in
                                 FStar_Util.Inr uu____23581))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____23659)::rest_a,(p1,uu____23662)::rest_p) ->
                       let uu____23706 = matches_pat t2 p1  in
                       (match uu____23706 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____23755 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____23873 = matches_pat scrutinee1 p1  in
                       (match uu____23873 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____23913  ->
                                  let uu____23914 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____23915 =
                                    let uu____23916 =
                                      FStar_List.map
                                        (fun uu____23926  ->
                                           match uu____23926 with
                                           | (uu____23931,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____23916
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____23914 uu____23915);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____23963  ->
                                       match uu____23963 with
                                       | (bv,t2) ->
                                           let uu____23986 =
                                             let uu____23993 =
                                               let uu____23996 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____23996
                                                in
                                             let uu____23997 =
                                               let uu____23998 =
                                                 let uu____24029 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____24029, false)
                                                  in
                                               Clos uu____23998  in
                                             (uu____23993, uu____23997)  in
                                           uu____23986 :: env2) env1 s
                                 in
                              let uu____24142 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____24142)))
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
    let uu____24169 =
      let uu____24172 = FStar_ST.op_Bang plugins  in p :: uu____24172  in
    FStar_ST.op_Colon_Equals plugins uu____24169  in
  let retrieve uu____24280 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____24357  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___94_24398  ->
                  match uu___94_24398 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____24402 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____24408 -> d  in
        let uu____24411 = to_fsteps s  in
        let uu____24412 =
          let uu____24413 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____24414 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____24415 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____24416 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____24417 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____24413;
            primop = uu____24414;
            b380 = uu____24415;
            norm_delayed = uu____24416;
            print_normalized = uu____24417
          }  in
        let uu____24418 =
          let uu____24421 =
            let uu____24424 = retrieve_plugins ()  in
            FStar_List.append uu____24424 psteps  in
          add_steps built_in_primitive_steps uu____24421  in
        let uu____24427 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____24429 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____24429)
           in
        {
          steps = uu____24411;
          tcenv = e;
          debug = uu____24412;
          delta_level = d1;
          primitive_steps = uu____24418;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____24427
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
      fun t  -> let uu____24511 = config s e  in norm_comp uu____24511 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____24528 = config [] env  in norm_universe uu____24528 [] u
  
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
        let uu____24552 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24552  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____24559 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___196_24578 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___196_24578.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___196_24578.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____24585 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____24585
          then
            let ct1 =
              let uu____24587 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____24587 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____24594 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____24594
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___197_24598 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___197_24598.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___197_24598.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___197_24598.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___198_24600 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___198_24600.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___198_24600.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___198_24600.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___198_24600.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___199_24601 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___199_24601.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___199_24601.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____24603 -> c
  
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
        let uu____24621 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24621  in
      let uu____24628 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____24628
      then
        let uu____24629 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____24629 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____24635  ->
                 let uu____24636 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____24636)
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
            ((let uu____24657 =
                let uu____24662 =
                  let uu____24663 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____24663
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____24662)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____24657);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____24678 = config [AllowUnboundUniverses] env  in
          norm_comp uu____24678 [] c
        with
        | e ->
            ((let uu____24691 =
                let uu____24696 =
                  let uu____24697 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____24697
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____24696)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____24691);
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
                   let uu____24742 =
                     let uu____24743 =
                       let uu____24750 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____24750)  in
                     FStar_Syntax_Syntax.Tm_refine uu____24743  in
                   mk uu____24742 t01.FStar_Syntax_Syntax.pos
               | uu____24755 -> t2)
          | uu____24756 -> t2  in
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
        let uu____24820 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____24820 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____24849 ->
                 let uu____24856 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____24856 with
                  | (actuals,uu____24866,uu____24867) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____24881 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____24881 with
                         | (binders,args) ->
                             let uu____24892 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____24892
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
      | uu____24906 ->
          let uu____24907 = FStar_Syntax_Util.head_and_args t  in
          (match uu____24907 with
           | (head1,args) ->
               let uu____24944 =
                 let uu____24945 = FStar_Syntax_Subst.compress head1  in
                 uu____24945.FStar_Syntax_Syntax.n  in
               (match uu____24944 with
                | FStar_Syntax_Syntax.Tm_uvar u ->
                    let uu____24949 =
                      FStar_Syntax_Util.arrow_formals
                        u.FStar_Syntax_Syntax.ctx_uvar_typ
                       in
                    (match uu____24949 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____24991 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___204_24999 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___204_24999.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___204_24999.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___204_24999.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___204_24999.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___204_24999.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___204_24999.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___204_24999.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___204_24999.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___204_24999.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___204_24999.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___204_24999.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___204_24999.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___204_24999.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___204_24999.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___204_24999.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___204_24999.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___204_24999.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___204_24999.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___204_24999.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___204_24999.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___204_24999.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___204_24999.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___204_24999.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___204_24999.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___204_24999.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___204_24999.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___204_24999.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___204_24999.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___204_24999.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___204_24999.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___204_24999.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___204_24999.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___204_24999.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___204_24999.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___204_24999.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____24991 with
                            | (uu____25000,ty,uu____25002) ->
                                eta_expand_with_type env t ty))
                | uu____25003 ->
                    let uu____25004 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___205_25012 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___205_25012.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___205_25012.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___205_25012.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___205_25012.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___205_25012.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___205_25012.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___205_25012.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___205_25012.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___205_25012.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___205_25012.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___205_25012.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___205_25012.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___205_25012.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___205_25012.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___205_25012.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___205_25012.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___205_25012.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___205_25012.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___205_25012.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___205_25012.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___205_25012.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___205_25012.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___205_25012.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___205_25012.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___205_25012.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___205_25012.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___205_25012.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___205_25012.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___205_25012.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___205_25012.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___205_25012.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___205_25012.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___205_25012.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___205_25012.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___205_25012.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____25004 with
                     | (uu____25013,ty,uu____25015) ->
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
      let uu___206_25088 = x  in
      let uu____25089 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___206_25088.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___206_25088.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____25089
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____25092 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____25117 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____25118 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____25119 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____25120 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____25127 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____25128 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____25129 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___207_25159 = rc  in
          let uu____25160 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____25169 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___207_25159.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____25160;
            FStar_Syntax_Syntax.residual_flags = uu____25169
          }  in
        let uu____25172 =
          let uu____25173 =
            let uu____25190 = elim_delayed_subst_binders bs  in
            let uu____25197 = elim_delayed_subst_term t2  in
            let uu____25200 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____25190, uu____25197, uu____25200)  in
          FStar_Syntax_Syntax.Tm_abs uu____25173  in
        mk1 uu____25172
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____25231 =
          let uu____25232 =
            let uu____25245 = elim_delayed_subst_binders bs  in
            let uu____25252 = elim_delayed_subst_comp c  in
            (uu____25245, uu____25252)  in
          FStar_Syntax_Syntax.Tm_arrow uu____25232  in
        mk1 uu____25231
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____25269 =
          let uu____25270 =
            let uu____25277 = elim_bv bv  in
            let uu____25278 = elim_delayed_subst_term phi  in
            (uu____25277, uu____25278)  in
          FStar_Syntax_Syntax.Tm_refine uu____25270  in
        mk1 uu____25269
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____25305 =
          let uu____25306 =
            let uu____25321 = elim_delayed_subst_term t2  in
            let uu____25324 = elim_delayed_subst_args args  in
            (uu____25321, uu____25324)  in
          FStar_Syntax_Syntax.Tm_app uu____25306  in
        mk1 uu____25305
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___208_25392 = p  in
              let uu____25393 =
                let uu____25394 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____25394  in
              {
                FStar_Syntax_Syntax.v = uu____25393;
                FStar_Syntax_Syntax.p =
                  (uu___208_25392.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___209_25396 = p  in
              let uu____25397 =
                let uu____25398 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____25398  in
              {
                FStar_Syntax_Syntax.v = uu____25397;
                FStar_Syntax_Syntax.p =
                  (uu___209_25396.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___210_25405 = p  in
              let uu____25406 =
                let uu____25407 =
                  let uu____25414 = elim_bv x  in
                  let uu____25415 = elim_delayed_subst_term t0  in
                  (uu____25414, uu____25415)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____25407  in
              {
                FStar_Syntax_Syntax.v = uu____25406;
                FStar_Syntax_Syntax.p =
                  (uu___210_25405.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___211_25438 = p  in
              let uu____25439 =
                let uu____25440 =
                  let uu____25453 =
                    FStar_List.map
                      (fun uu____25476  ->
                         match uu____25476 with
                         | (x,b) ->
                             let uu____25489 = elim_pat x  in
                             (uu____25489, b)) pats
                     in
                  (fv, uu____25453)  in
                FStar_Syntax_Syntax.Pat_cons uu____25440  in
              {
                FStar_Syntax_Syntax.v = uu____25439;
                FStar_Syntax_Syntax.p =
                  (uu___211_25438.FStar_Syntax_Syntax.p)
              }
          | uu____25502 -> p  in
        let elim_branch uu____25526 =
          match uu____25526 with
          | (pat,wopt,t3) ->
              let uu____25552 = elim_pat pat  in
              let uu____25555 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____25558 = elim_delayed_subst_term t3  in
              (uu____25552, uu____25555, uu____25558)
           in
        let uu____25563 =
          let uu____25564 =
            let uu____25587 = elim_delayed_subst_term t2  in
            let uu____25590 = FStar_List.map elim_branch branches  in
            (uu____25587, uu____25590)  in
          FStar_Syntax_Syntax.Tm_match uu____25564  in
        mk1 uu____25563
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____25717 =
          match uu____25717 with
          | (tc,topt) ->
              let uu____25752 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____25762 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____25762
                | FStar_Util.Inr c ->
                    let uu____25764 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____25764
                 in
              let uu____25765 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____25752, uu____25765)
           in
        let uu____25774 =
          let uu____25775 =
            let uu____25802 = elim_delayed_subst_term t2  in
            let uu____25805 = elim_ascription a  in
            (uu____25802, uu____25805, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____25775  in
        mk1 uu____25774
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___212_25866 = lb  in
          let uu____25867 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____25870 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___212_25866.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___212_25866.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____25867;
            FStar_Syntax_Syntax.lbeff =
              (uu___212_25866.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____25870;
            FStar_Syntax_Syntax.lbattrs =
              (uu___212_25866.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___212_25866.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____25873 =
          let uu____25874 =
            let uu____25887 =
              let uu____25894 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____25894)  in
            let uu____25903 = elim_delayed_subst_term t2  in
            (uu____25887, uu____25903)  in
          FStar_Syntax_Syntax.Tm_let uu____25874  in
        mk1 uu____25873
    | FStar_Syntax_Syntax.Tm_uvar u -> mk1 (FStar_Syntax_Syntax.Tm_uvar u)
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____25922 =
          let uu____25923 =
            let uu____25930 = elim_delayed_subst_term tm  in
            (uu____25930, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____25923  in
        mk1 uu____25922
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____25941 =
          let uu____25942 =
            let uu____25949 = elim_delayed_subst_term t2  in
            let uu____25952 = elim_delayed_subst_meta md  in
            (uu____25949, uu____25952)  in
          FStar_Syntax_Syntax.Tm_meta uu____25942  in
        mk1 uu____25941

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___95_25961  ->
         match uu___95_25961 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____25965 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____25965
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
        let uu____25988 =
          let uu____25989 =
            let uu____25998 = elim_delayed_subst_term t  in
            (uu____25998, uopt)  in
          FStar_Syntax_Syntax.Total uu____25989  in
        mk1 uu____25988
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____26015 =
          let uu____26016 =
            let uu____26025 = elim_delayed_subst_term t  in
            (uu____26025, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____26016  in
        mk1 uu____26015
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___213_26034 = ct  in
          let uu____26035 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____26038 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____26047 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___213_26034.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___213_26034.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____26035;
            FStar_Syntax_Syntax.effect_args = uu____26038;
            FStar_Syntax_Syntax.flags = uu____26047
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___96_26050  ->
    match uu___96_26050 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____26062 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____26062
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____26095 =
          let uu____26102 = elim_delayed_subst_term t  in (m, uu____26102)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____26095
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____26114 =
          let uu____26123 = elim_delayed_subst_term t  in
          (m1, m2, uu____26123)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____26114
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____26150  ->
         match uu____26150 with
         | (t,q) ->
             let uu____26161 = elim_delayed_subst_term t  in (uu____26161, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____26181  ->
         match uu____26181 with
         | (x,q) ->
             let uu____26192 =
               let uu___214_26193 = x  in
               let uu____26194 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___214_26193.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___214_26193.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____26194
               }  in
             (uu____26192, q)) bs

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
            | (uu____26284,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____26310,FStar_Util.Inl t) ->
                let uu____26328 =
                  let uu____26335 =
                    let uu____26336 =
                      let uu____26349 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____26349)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____26336  in
                  FStar_Syntax_Syntax.mk uu____26335  in
                uu____26328 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____26363 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____26363 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____26391 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____26446 ->
                    let uu____26447 =
                      let uu____26456 =
                        let uu____26457 = FStar_Syntax_Subst.compress t4  in
                        uu____26457.FStar_Syntax_Syntax.n  in
                      (uu____26456, tc)  in
                    (match uu____26447 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____26482) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____26519) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____26558,FStar_Util.Inl uu____26559) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____26582 -> failwith "Impossible")
                 in
              (match uu____26391 with
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
          let uu____26695 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____26695 with
          | (univ_names1,binders1,tc) ->
              let uu____26753 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____26753)
  
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
          let uu____26796 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____26796 with
          | (univ_names1,binders1,tc) ->
              let uu____26856 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____26856)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____26893 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____26893 with
           | (univ_names1,binders1,typ1) ->
               let uu___215_26921 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___215_26921.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___215_26921.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___215_26921.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___215_26921.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___216_26936 = s  in
          let uu____26937 =
            let uu____26938 =
              let uu____26947 = FStar_List.map (elim_uvars env) sigs  in
              (uu____26947, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____26938  in
          {
            FStar_Syntax_Syntax.sigel = uu____26937;
            FStar_Syntax_Syntax.sigrng =
              (uu___216_26936.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___216_26936.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___216_26936.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___216_26936.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____26964 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____26964 with
           | (univ_names1,uu____26982,typ1) ->
               let uu___217_26996 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___217_26996.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___217_26996.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___217_26996.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___217_26996.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____27002 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27002 with
           | (univ_names1,uu____27020,typ1) ->
               let uu___218_27034 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___218_27034.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___218_27034.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___218_27034.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___218_27034.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____27062 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____27062 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____27087 =
                            let uu____27088 =
                              let uu____27089 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____27089  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____27088
                             in
                          elim_delayed_subst_term uu____27087  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___219_27092 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___219_27092.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___219_27092.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___219_27092.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___219_27092.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___220_27093 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___220_27093.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___220_27093.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___220_27093.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___220_27093.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___221_27099 = s  in
          let uu____27100 =
            let uu____27101 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____27101  in
          {
            FStar_Syntax_Syntax.sigel = uu____27100;
            FStar_Syntax_Syntax.sigrng =
              (uu___221_27099.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___221_27099.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___221_27099.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___221_27099.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____27105 = elim_uvars_aux_t env us [] t  in
          (match uu____27105 with
           | (us1,uu____27123,t1) ->
               let uu___222_27137 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___222_27137.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___222_27137.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___222_27137.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___222_27137.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____27138 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____27140 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____27140 with
           | (univs1,binders,signature) ->
               let uu____27168 =
                 let uu____27177 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____27177 with
                 | (univs_opening,univs2) ->
                     let uu____27204 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____27204)
                  in
               (match uu____27168 with
                | (univs_opening,univs_closing) ->
                    let uu____27221 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____27227 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____27228 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____27227, uu____27228)  in
                    (match uu____27221 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____27252 =
                           match uu____27252 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____27270 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____27270 with
                                | (us1,t1) ->
                                    let uu____27281 =
                                      let uu____27290 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____27301 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____27290, uu____27301)  in
                                    (match uu____27281 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____27330 =
                                           let uu____27339 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____27350 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____27339, uu____27350)  in
                                         (match uu____27330 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____27380 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____27380
                                                 in
                                              let uu____27381 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____27381 with
                                               | (uu____27402,uu____27403,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____27418 =
                                                       let uu____27419 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____27419
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____27418
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____27426 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____27426 with
                           | (uu____27439,uu____27440,t1) -> t1  in
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
                             | uu____27510 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____27535 =
                               let uu____27536 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____27536.FStar_Syntax_Syntax.n  in
                             match uu____27535 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____27595 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____27626 =
                               let uu____27627 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____27627.FStar_Syntax_Syntax.n  in
                             match uu____27626 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____27648) ->
                                 let uu____27669 = destruct_action_body body
                                    in
                                 (match uu____27669 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____27714 ->
                                 let uu____27715 = destruct_action_body t  in
                                 (match uu____27715 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____27764 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____27764 with
                           | (action_univs,t) ->
                               let uu____27773 = destruct_action_typ_templ t
                                  in
                               (match uu____27773 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___223_27814 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___223_27814.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___223_27814.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___224_27816 = ed  in
                           let uu____27817 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____27818 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____27819 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____27820 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____27821 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____27822 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____27823 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____27824 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____27825 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____27826 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____27827 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____27828 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____27829 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____27830 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___224_27816.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___224_27816.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____27817;
                             FStar_Syntax_Syntax.bind_wp = uu____27818;
                             FStar_Syntax_Syntax.if_then_else = uu____27819;
                             FStar_Syntax_Syntax.ite_wp = uu____27820;
                             FStar_Syntax_Syntax.stronger = uu____27821;
                             FStar_Syntax_Syntax.close_wp = uu____27822;
                             FStar_Syntax_Syntax.assert_p = uu____27823;
                             FStar_Syntax_Syntax.assume_p = uu____27824;
                             FStar_Syntax_Syntax.null_wp = uu____27825;
                             FStar_Syntax_Syntax.trivial = uu____27826;
                             FStar_Syntax_Syntax.repr = uu____27827;
                             FStar_Syntax_Syntax.return_repr = uu____27828;
                             FStar_Syntax_Syntax.bind_repr = uu____27829;
                             FStar_Syntax_Syntax.actions = uu____27830;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___224_27816.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___225_27833 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___225_27833.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___225_27833.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___225_27833.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___225_27833.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___97_27852 =
            match uu___97_27852 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____27879 = elim_uvars_aux_t env us [] t  in
                (match uu____27879 with
                 | (us1,uu____27903,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___226_27922 = sub_eff  in
            let uu____27923 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____27926 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___226_27922.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___226_27922.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____27923;
              FStar_Syntax_Syntax.lift = uu____27926
            }  in
          let uu___227_27929 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___227_27929.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___227_27929.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___227_27929.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___227_27929.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____27939 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____27939 with
           | (univ_names1,binders1,comp1) ->
               let uu___228_27973 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___228_27973.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___228_27973.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___228_27973.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___228_27973.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____27976 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____27977 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  