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
      fun uu___106_269  ->
        match uu___106_269 with
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
      let add_opt x uu___107_1503 =
        match uu___107_1503 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___126_1523 = fs  in
          {
            beta = true;
            iota = (uu___126_1523.iota);
            zeta = (uu___126_1523.zeta);
            weak = (uu___126_1523.weak);
            hnf = (uu___126_1523.hnf);
            primops = (uu___126_1523.primops);
            do_not_unfold_pure_lets = (uu___126_1523.do_not_unfold_pure_lets);
            unfold_until = (uu___126_1523.unfold_until);
            unfold_only = (uu___126_1523.unfold_only);
            unfold_fully = (uu___126_1523.unfold_fully);
            unfold_attr = (uu___126_1523.unfold_attr);
            unfold_tac = (uu___126_1523.unfold_tac);
            pure_subterms_within_computations =
              (uu___126_1523.pure_subterms_within_computations);
            simplify = (uu___126_1523.simplify);
            erase_universes = (uu___126_1523.erase_universes);
            allow_unbound_universes = (uu___126_1523.allow_unbound_universes);
            reify_ = (uu___126_1523.reify_);
            compress_uvars = (uu___126_1523.compress_uvars);
            no_full_norm = (uu___126_1523.no_full_norm);
            check_no_uvars = (uu___126_1523.check_no_uvars);
            unmeta = (uu___126_1523.unmeta);
            unascribe = (uu___126_1523.unascribe);
            in_full_norm_request = (uu___126_1523.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___126_1523.weakly_reduce_scrutinee)
          }
      | Iota  ->
          let uu___127_1524 = fs  in
          {
            beta = (uu___127_1524.beta);
            iota = true;
            zeta = (uu___127_1524.zeta);
            weak = (uu___127_1524.weak);
            hnf = (uu___127_1524.hnf);
            primops = (uu___127_1524.primops);
            do_not_unfold_pure_lets = (uu___127_1524.do_not_unfold_pure_lets);
            unfold_until = (uu___127_1524.unfold_until);
            unfold_only = (uu___127_1524.unfold_only);
            unfold_fully = (uu___127_1524.unfold_fully);
            unfold_attr = (uu___127_1524.unfold_attr);
            unfold_tac = (uu___127_1524.unfold_tac);
            pure_subterms_within_computations =
              (uu___127_1524.pure_subterms_within_computations);
            simplify = (uu___127_1524.simplify);
            erase_universes = (uu___127_1524.erase_universes);
            allow_unbound_universes = (uu___127_1524.allow_unbound_universes);
            reify_ = (uu___127_1524.reify_);
            compress_uvars = (uu___127_1524.compress_uvars);
            no_full_norm = (uu___127_1524.no_full_norm);
            check_no_uvars = (uu___127_1524.check_no_uvars);
            unmeta = (uu___127_1524.unmeta);
            unascribe = (uu___127_1524.unascribe);
            in_full_norm_request = (uu___127_1524.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___127_1524.weakly_reduce_scrutinee)
          }
      | Zeta  ->
          let uu___128_1525 = fs  in
          {
            beta = (uu___128_1525.beta);
            iota = (uu___128_1525.iota);
            zeta = true;
            weak = (uu___128_1525.weak);
            hnf = (uu___128_1525.hnf);
            primops = (uu___128_1525.primops);
            do_not_unfold_pure_lets = (uu___128_1525.do_not_unfold_pure_lets);
            unfold_until = (uu___128_1525.unfold_until);
            unfold_only = (uu___128_1525.unfold_only);
            unfold_fully = (uu___128_1525.unfold_fully);
            unfold_attr = (uu___128_1525.unfold_attr);
            unfold_tac = (uu___128_1525.unfold_tac);
            pure_subterms_within_computations =
              (uu___128_1525.pure_subterms_within_computations);
            simplify = (uu___128_1525.simplify);
            erase_universes = (uu___128_1525.erase_universes);
            allow_unbound_universes = (uu___128_1525.allow_unbound_universes);
            reify_ = (uu___128_1525.reify_);
            compress_uvars = (uu___128_1525.compress_uvars);
            no_full_norm = (uu___128_1525.no_full_norm);
            check_no_uvars = (uu___128_1525.check_no_uvars);
            unmeta = (uu___128_1525.unmeta);
            unascribe = (uu___128_1525.unascribe);
            in_full_norm_request = (uu___128_1525.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___128_1525.weakly_reduce_scrutinee)
          }
      | Exclude (Beta ) ->
          let uu___129_1526 = fs  in
          {
            beta = false;
            iota = (uu___129_1526.iota);
            zeta = (uu___129_1526.zeta);
            weak = (uu___129_1526.weak);
            hnf = (uu___129_1526.hnf);
            primops = (uu___129_1526.primops);
            do_not_unfold_pure_lets = (uu___129_1526.do_not_unfold_pure_lets);
            unfold_until = (uu___129_1526.unfold_until);
            unfold_only = (uu___129_1526.unfold_only);
            unfold_fully = (uu___129_1526.unfold_fully);
            unfold_attr = (uu___129_1526.unfold_attr);
            unfold_tac = (uu___129_1526.unfold_tac);
            pure_subterms_within_computations =
              (uu___129_1526.pure_subterms_within_computations);
            simplify = (uu___129_1526.simplify);
            erase_universes = (uu___129_1526.erase_universes);
            allow_unbound_universes = (uu___129_1526.allow_unbound_universes);
            reify_ = (uu___129_1526.reify_);
            compress_uvars = (uu___129_1526.compress_uvars);
            no_full_norm = (uu___129_1526.no_full_norm);
            check_no_uvars = (uu___129_1526.check_no_uvars);
            unmeta = (uu___129_1526.unmeta);
            unascribe = (uu___129_1526.unascribe);
            in_full_norm_request = (uu___129_1526.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___129_1526.weakly_reduce_scrutinee)
          }
      | Exclude (Iota ) ->
          let uu___130_1527 = fs  in
          {
            beta = (uu___130_1527.beta);
            iota = false;
            zeta = (uu___130_1527.zeta);
            weak = (uu___130_1527.weak);
            hnf = (uu___130_1527.hnf);
            primops = (uu___130_1527.primops);
            do_not_unfold_pure_lets = (uu___130_1527.do_not_unfold_pure_lets);
            unfold_until = (uu___130_1527.unfold_until);
            unfold_only = (uu___130_1527.unfold_only);
            unfold_fully = (uu___130_1527.unfold_fully);
            unfold_attr = (uu___130_1527.unfold_attr);
            unfold_tac = (uu___130_1527.unfold_tac);
            pure_subterms_within_computations =
              (uu___130_1527.pure_subterms_within_computations);
            simplify = (uu___130_1527.simplify);
            erase_universes = (uu___130_1527.erase_universes);
            allow_unbound_universes = (uu___130_1527.allow_unbound_universes);
            reify_ = (uu___130_1527.reify_);
            compress_uvars = (uu___130_1527.compress_uvars);
            no_full_norm = (uu___130_1527.no_full_norm);
            check_no_uvars = (uu___130_1527.check_no_uvars);
            unmeta = (uu___130_1527.unmeta);
            unascribe = (uu___130_1527.unascribe);
            in_full_norm_request = (uu___130_1527.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___130_1527.weakly_reduce_scrutinee)
          }
      | Exclude (Zeta ) ->
          let uu___131_1528 = fs  in
          {
            beta = (uu___131_1528.beta);
            iota = (uu___131_1528.iota);
            zeta = false;
            weak = (uu___131_1528.weak);
            hnf = (uu___131_1528.hnf);
            primops = (uu___131_1528.primops);
            do_not_unfold_pure_lets = (uu___131_1528.do_not_unfold_pure_lets);
            unfold_until = (uu___131_1528.unfold_until);
            unfold_only = (uu___131_1528.unfold_only);
            unfold_fully = (uu___131_1528.unfold_fully);
            unfold_attr = (uu___131_1528.unfold_attr);
            unfold_tac = (uu___131_1528.unfold_tac);
            pure_subterms_within_computations =
              (uu___131_1528.pure_subterms_within_computations);
            simplify = (uu___131_1528.simplify);
            erase_universes = (uu___131_1528.erase_universes);
            allow_unbound_universes = (uu___131_1528.allow_unbound_universes);
            reify_ = (uu___131_1528.reify_);
            compress_uvars = (uu___131_1528.compress_uvars);
            no_full_norm = (uu___131_1528.no_full_norm);
            check_no_uvars = (uu___131_1528.check_no_uvars);
            unmeta = (uu___131_1528.unmeta);
            unascribe = (uu___131_1528.unascribe);
            in_full_norm_request = (uu___131_1528.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___131_1528.weakly_reduce_scrutinee)
          }
      | Exclude uu____1529 -> failwith "Bad exclude"
      | Weak  ->
          let uu___132_1530 = fs  in
          {
            beta = (uu___132_1530.beta);
            iota = (uu___132_1530.iota);
            zeta = (uu___132_1530.zeta);
            weak = true;
            hnf = (uu___132_1530.hnf);
            primops = (uu___132_1530.primops);
            do_not_unfold_pure_lets = (uu___132_1530.do_not_unfold_pure_lets);
            unfold_until = (uu___132_1530.unfold_until);
            unfold_only = (uu___132_1530.unfold_only);
            unfold_fully = (uu___132_1530.unfold_fully);
            unfold_attr = (uu___132_1530.unfold_attr);
            unfold_tac = (uu___132_1530.unfold_tac);
            pure_subterms_within_computations =
              (uu___132_1530.pure_subterms_within_computations);
            simplify = (uu___132_1530.simplify);
            erase_universes = (uu___132_1530.erase_universes);
            allow_unbound_universes = (uu___132_1530.allow_unbound_universes);
            reify_ = (uu___132_1530.reify_);
            compress_uvars = (uu___132_1530.compress_uvars);
            no_full_norm = (uu___132_1530.no_full_norm);
            check_no_uvars = (uu___132_1530.check_no_uvars);
            unmeta = (uu___132_1530.unmeta);
            unascribe = (uu___132_1530.unascribe);
            in_full_norm_request = (uu___132_1530.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___132_1530.weakly_reduce_scrutinee)
          }
      | HNF  ->
          let uu___133_1531 = fs  in
          {
            beta = (uu___133_1531.beta);
            iota = (uu___133_1531.iota);
            zeta = (uu___133_1531.zeta);
            weak = (uu___133_1531.weak);
            hnf = true;
            primops = (uu___133_1531.primops);
            do_not_unfold_pure_lets = (uu___133_1531.do_not_unfold_pure_lets);
            unfold_until = (uu___133_1531.unfold_until);
            unfold_only = (uu___133_1531.unfold_only);
            unfold_fully = (uu___133_1531.unfold_fully);
            unfold_attr = (uu___133_1531.unfold_attr);
            unfold_tac = (uu___133_1531.unfold_tac);
            pure_subterms_within_computations =
              (uu___133_1531.pure_subterms_within_computations);
            simplify = (uu___133_1531.simplify);
            erase_universes = (uu___133_1531.erase_universes);
            allow_unbound_universes = (uu___133_1531.allow_unbound_universes);
            reify_ = (uu___133_1531.reify_);
            compress_uvars = (uu___133_1531.compress_uvars);
            no_full_norm = (uu___133_1531.no_full_norm);
            check_no_uvars = (uu___133_1531.check_no_uvars);
            unmeta = (uu___133_1531.unmeta);
            unascribe = (uu___133_1531.unascribe);
            in_full_norm_request = (uu___133_1531.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___133_1531.weakly_reduce_scrutinee)
          }
      | Primops  ->
          let uu___134_1532 = fs  in
          {
            beta = (uu___134_1532.beta);
            iota = (uu___134_1532.iota);
            zeta = (uu___134_1532.zeta);
            weak = (uu___134_1532.weak);
            hnf = (uu___134_1532.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___134_1532.do_not_unfold_pure_lets);
            unfold_until = (uu___134_1532.unfold_until);
            unfold_only = (uu___134_1532.unfold_only);
            unfold_fully = (uu___134_1532.unfold_fully);
            unfold_attr = (uu___134_1532.unfold_attr);
            unfold_tac = (uu___134_1532.unfold_tac);
            pure_subterms_within_computations =
              (uu___134_1532.pure_subterms_within_computations);
            simplify = (uu___134_1532.simplify);
            erase_universes = (uu___134_1532.erase_universes);
            allow_unbound_universes = (uu___134_1532.allow_unbound_universes);
            reify_ = (uu___134_1532.reify_);
            compress_uvars = (uu___134_1532.compress_uvars);
            no_full_norm = (uu___134_1532.no_full_norm);
            check_no_uvars = (uu___134_1532.check_no_uvars);
            unmeta = (uu___134_1532.unmeta);
            unascribe = (uu___134_1532.unascribe);
            in_full_norm_request = (uu___134_1532.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___134_1532.weakly_reduce_scrutinee)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___135_1533 = fs  in
          {
            beta = (uu___135_1533.beta);
            iota = (uu___135_1533.iota);
            zeta = (uu___135_1533.zeta);
            weak = (uu___135_1533.weak);
            hnf = (uu___135_1533.hnf);
            primops = (uu___135_1533.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___135_1533.unfold_until);
            unfold_only = (uu___135_1533.unfold_only);
            unfold_fully = (uu___135_1533.unfold_fully);
            unfold_attr = (uu___135_1533.unfold_attr);
            unfold_tac = (uu___135_1533.unfold_tac);
            pure_subterms_within_computations =
              (uu___135_1533.pure_subterms_within_computations);
            simplify = (uu___135_1533.simplify);
            erase_universes = (uu___135_1533.erase_universes);
            allow_unbound_universes = (uu___135_1533.allow_unbound_universes);
            reify_ = (uu___135_1533.reify_);
            compress_uvars = (uu___135_1533.compress_uvars);
            no_full_norm = (uu___135_1533.no_full_norm);
            check_no_uvars = (uu___135_1533.check_no_uvars);
            unmeta = (uu___135_1533.unmeta);
            unascribe = (uu___135_1533.unascribe);
            in_full_norm_request = (uu___135_1533.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___135_1533.weakly_reduce_scrutinee)
          }
      | UnfoldUntil d ->
          let uu___136_1535 = fs  in
          {
            beta = (uu___136_1535.beta);
            iota = (uu___136_1535.iota);
            zeta = (uu___136_1535.zeta);
            weak = (uu___136_1535.weak);
            hnf = (uu___136_1535.hnf);
            primops = (uu___136_1535.primops);
            do_not_unfold_pure_lets = (uu___136_1535.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___136_1535.unfold_only);
            unfold_fully = (uu___136_1535.unfold_fully);
            unfold_attr = (uu___136_1535.unfold_attr);
            unfold_tac = (uu___136_1535.unfold_tac);
            pure_subterms_within_computations =
              (uu___136_1535.pure_subterms_within_computations);
            simplify = (uu___136_1535.simplify);
            erase_universes = (uu___136_1535.erase_universes);
            allow_unbound_universes = (uu___136_1535.allow_unbound_universes);
            reify_ = (uu___136_1535.reify_);
            compress_uvars = (uu___136_1535.compress_uvars);
            no_full_norm = (uu___136_1535.no_full_norm);
            check_no_uvars = (uu___136_1535.check_no_uvars);
            unmeta = (uu___136_1535.unmeta);
            unascribe = (uu___136_1535.unascribe);
            in_full_norm_request = (uu___136_1535.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___136_1535.weakly_reduce_scrutinee)
          }
      | UnfoldOnly lids ->
          let uu___137_1539 = fs  in
          {
            beta = (uu___137_1539.beta);
            iota = (uu___137_1539.iota);
            zeta = (uu___137_1539.zeta);
            weak = (uu___137_1539.weak);
            hnf = (uu___137_1539.hnf);
            primops = (uu___137_1539.primops);
            do_not_unfold_pure_lets = (uu___137_1539.do_not_unfold_pure_lets);
            unfold_until = (uu___137_1539.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___137_1539.unfold_fully);
            unfold_attr = (uu___137_1539.unfold_attr);
            unfold_tac = (uu___137_1539.unfold_tac);
            pure_subterms_within_computations =
              (uu___137_1539.pure_subterms_within_computations);
            simplify = (uu___137_1539.simplify);
            erase_universes = (uu___137_1539.erase_universes);
            allow_unbound_universes = (uu___137_1539.allow_unbound_universes);
            reify_ = (uu___137_1539.reify_);
            compress_uvars = (uu___137_1539.compress_uvars);
            no_full_norm = (uu___137_1539.no_full_norm);
            check_no_uvars = (uu___137_1539.check_no_uvars);
            unmeta = (uu___137_1539.unmeta);
            unascribe = (uu___137_1539.unascribe);
            in_full_norm_request = (uu___137_1539.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___137_1539.weakly_reduce_scrutinee)
          }
      | UnfoldFully lids ->
          let uu___138_1545 = fs  in
          {
            beta = (uu___138_1545.beta);
            iota = (uu___138_1545.iota);
            zeta = (uu___138_1545.zeta);
            weak = (uu___138_1545.weak);
            hnf = (uu___138_1545.hnf);
            primops = (uu___138_1545.primops);
            do_not_unfold_pure_lets = (uu___138_1545.do_not_unfold_pure_lets);
            unfold_until = (uu___138_1545.unfold_until);
            unfold_only = (uu___138_1545.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___138_1545.unfold_attr);
            unfold_tac = (uu___138_1545.unfold_tac);
            pure_subterms_within_computations =
              (uu___138_1545.pure_subterms_within_computations);
            simplify = (uu___138_1545.simplify);
            erase_universes = (uu___138_1545.erase_universes);
            allow_unbound_universes = (uu___138_1545.allow_unbound_universes);
            reify_ = (uu___138_1545.reify_);
            compress_uvars = (uu___138_1545.compress_uvars);
            no_full_norm = (uu___138_1545.no_full_norm);
            check_no_uvars = (uu___138_1545.check_no_uvars);
            unmeta = (uu___138_1545.unmeta);
            unascribe = (uu___138_1545.unascribe);
            in_full_norm_request = (uu___138_1545.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___138_1545.weakly_reduce_scrutinee)
          }
      | UnfoldAttr attr ->
          let uu___139_1549 = fs  in
          {
            beta = (uu___139_1549.beta);
            iota = (uu___139_1549.iota);
            zeta = (uu___139_1549.zeta);
            weak = (uu___139_1549.weak);
            hnf = (uu___139_1549.hnf);
            primops = (uu___139_1549.primops);
            do_not_unfold_pure_lets = (uu___139_1549.do_not_unfold_pure_lets);
            unfold_until = (uu___139_1549.unfold_until);
            unfold_only = (uu___139_1549.unfold_only);
            unfold_fully = (uu___139_1549.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___139_1549.unfold_tac);
            pure_subterms_within_computations =
              (uu___139_1549.pure_subterms_within_computations);
            simplify = (uu___139_1549.simplify);
            erase_universes = (uu___139_1549.erase_universes);
            allow_unbound_universes = (uu___139_1549.allow_unbound_universes);
            reify_ = (uu___139_1549.reify_);
            compress_uvars = (uu___139_1549.compress_uvars);
            no_full_norm = (uu___139_1549.no_full_norm);
            check_no_uvars = (uu___139_1549.check_no_uvars);
            unmeta = (uu___139_1549.unmeta);
            unascribe = (uu___139_1549.unascribe);
            in_full_norm_request = (uu___139_1549.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___139_1549.weakly_reduce_scrutinee)
          }
      | UnfoldTac  ->
          let uu___140_1550 = fs  in
          {
            beta = (uu___140_1550.beta);
            iota = (uu___140_1550.iota);
            zeta = (uu___140_1550.zeta);
            weak = (uu___140_1550.weak);
            hnf = (uu___140_1550.hnf);
            primops = (uu___140_1550.primops);
            do_not_unfold_pure_lets = (uu___140_1550.do_not_unfold_pure_lets);
            unfold_until = (uu___140_1550.unfold_until);
            unfold_only = (uu___140_1550.unfold_only);
            unfold_fully = (uu___140_1550.unfold_fully);
            unfold_attr = (uu___140_1550.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___140_1550.pure_subterms_within_computations);
            simplify = (uu___140_1550.simplify);
            erase_universes = (uu___140_1550.erase_universes);
            allow_unbound_universes = (uu___140_1550.allow_unbound_universes);
            reify_ = (uu___140_1550.reify_);
            compress_uvars = (uu___140_1550.compress_uvars);
            no_full_norm = (uu___140_1550.no_full_norm);
            check_no_uvars = (uu___140_1550.check_no_uvars);
            unmeta = (uu___140_1550.unmeta);
            unascribe = (uu___140_1550.unascribe);
            in_full_norm_request = (uu___140_1550.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___140_1550.weakly_reduce_scrutinee)
          }
      | PureSubtermsWithinComputations  ->
          let uu___141_1551 = fs  in
          {
            beta = (uu___141_1551.beta);
            iota = (uu___141_1551.iota);
            zeta = (uu___141_1551.zeta);
            weak = (uu___141_1551.weak);
            hnf = (uu___141_1551.hnf);
            primops = (uu___141_1551.primops);
            do_not_unfold_pure_lets = (uu___141_1551.do_not_unfold_pure_lets);
            unfold_until = (uu___141_1551.unfold_until);
            unfold_only = (uu___141_1551.unfold_only);
            unfold_fully = (uu___141_1551.unfold_fully);
            unfold_attr = (uu___141_1551.unfold_attr);
            unfold_tac = (uu___141_1551.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___141_1551.simplify);
            erase_universes = (uu___141_1551.erase_universes);
            allow_unbound_universes = (uu___141_1551.allow_unbound_universes);
            reify_ = (uu___141_1551.reify_);
            compress_uvars = (uu___141_1551.compress_uvars);
            no_full_norm = (uu___141_1551.no_full_norm);
            check_no_uvars = (uu___141_1551.check_no_uvars);
            unmeta = (uu___141_1551.unmeta);
            unascribe = (uu___141_1551.unascribe);
            in_full_norm_request = (uu___141_1551.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___141_1551.weakly_reduce_scrutinee)
          }
      | Simplify  ->
          let uu___142_1552 = fs  in
          {
            beta = (uu___142_1552.beta);
            iota = (uu___142_1552.iota);
            zeta = (uu___142_1552.zeta);
            weak = (uu___142_1552.weak);
            hnf = (uu___142_1552.hnf);
            primops = (uu___142_1552.primops);
            do_not_unfold_pure_lets = (uu___142_1552.do_not_unfold_pure_lets);
            unfold_until = (uu___142_1552.unfold_until);
            unfold_only = (uu___142_1552.unfold_only);
            unfold_fully = (uu___142_1552.unfold_fully);
            unfold_attr = (uu___142_1552.unfold_attr);
            unfold_tac = (uu___142_1552.unfold_tac);
            pure_subterms_within_computations =
              (uu___142_1552.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___142_1552.erase_universes);
            allow_unbound_universes = (uu___142_1552.allow_unbound_universes);
            reify_ = (uu___142_1552.reify_);
            compress_uvars = (uu___142_1552.compress_uvars);
            no_full_norm = (uu___142_1552.no_full_norm);
            check_no_uvars = (uu___142_1552.check_no_uvars);
            unmeta = (uu___142_1552.unmeta);
            unascribe = (uu___142_1552.unascribe);
            in_full_norm_request = (uu___142_1552.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___142_1552.weakly_reduce_scrutinee)
          }
      | EraseUniverses  ->
          let uu___143_1553 = fs  in
          {
            beta = (uu___143_1553.beta);
            iota = (uu___143_1553.iota);
            zeta = (uu___143_1553.zeta);
            weak = (uu___143_1553.weak);
            hnf = (uu___143_1553.hnf);
            primops = (uu___143_1553.primops);
            do_not_unfold_pure_lets = (uu___143_1553.do_not_unfold_pure_lets);
            unfold_until = (uu___143_1553.unfold_until);
            unfold_only = (uu___143_1553.unfold_only);
            unfold_fully = (uu___143_1553.unfold_fully);
            unfold_attr = (uu___143_1553.unfold_attr);
            unfold_tac = (uu___143_1553.unfold_tac);
            pure_subterms_within_computations =
              (uu___143_1553.pure_subterms_within_computations);
            simplify = (uu___143_1553.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___143_1553.allow_unbound_universes);
            reify_ = (uu___143_1553.reify_);
            compress_uvars = (uu___143_1553.compress_uvars);
            no_full_norm = (uu___143_1553.no_full_norm);
            check_no_uvars = (uu___143_1553.check_no_uvars);
            unmeta = (uu___143_1553.unmeta);
            unascribe = (uu___143_1553.unascribe);
            in_full_norm_request = (uu___143_1553.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___143_1553.weakly_reduce_scrutinee)
          }
      | AllowUnboundUniverses  ->
          let uu___144_1554 = fs  in
          {
            beta = (uu___144_1554.beta);
            iota = (uu___144_1554.iota);
            zeta = (uu___144_1554.zeta);
            weak = (uu___144_1554.weak);
            hnf = (uu___144_1554.hnf);
            primops = (uu___144_1554.primops);
            do_not_unfold_pure_lets = (uu___144_1554.do_not_unfold_pure_lets);
            unfold_until = (uu___144_1554.unfold_until);
            unfold_only = (uu___144_1554.unfold_only);
            unfold_fully = (uu___144_1554.unfold_fully);
            unfold_attr = (uu___144_1554.unfold_attr);
            unfold_tac = (uu___144_1554.unfold_tac);
            pure_subterms_within_computations =
              (uu___144_1554.pure_subterms_within_computations);
            simplify = (uu___144_1554.simplify);
            erase_universes = (uu___144_1554.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___144_1554.reify_);
            compress_uvars = (uu___144_1554.compress_uvars);
            no_full_norm = (uu___144_1554.no_full_norm);
            check_no_uvars = (uu___144_1554.check_no_uvars);
            unmeta = (uu___144_1554.unmeta);
            unascribe = (uu___144_1554.unascribe);
            in_full_norm_request = (uu___144_1554.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___144_1554.weakly_reduce_scrutinee)
          }
      | Reify  ->
          let uu___145_1555 = fs  in
          {
            beta = (uu___145_1555.beta);
            iota = (uu___145_1555.iota);
            zeta = (uu___145_1555.zeta);
            weak = (uu___145_1555.weak);
            hnf = (uu___145_1555.hnf);
            primops = (uu___145_1555.primops);
            do_not_unfold_pure_lets = (uu___145_1555.do_not_unfold_pure_lets);
            unfold_until = (uu___145_1555.unfold_until);
            unfold_only = (uu___145_1555.unfold_only);
            unfold_fully = (uu___145_1555.unfold_fully);
            unfold_attr = (uu___145_1555.unfold_attr);
            unfold_tac = (uu___145_1555.unfold_tac);
            pure_subterms_within_computations =
              (uu___145_1555.pure_subterms_within_computations);
            simplify = (uu___145_1555.simplify);
            erase_universes = (uu___145_1555.erase_universes);
            allow_unbound_universes = (uu___145_1555.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___145_1555.compress_uvars);
            no_full_norm = (uu___145_1555.no_full_norm);
            check_no_uvars = (uu___145_1555.check_no_uvars);
            unmeta = (uu___145_1555.unmeta);
            unascribe = (uu___145_1555.unascribe);
            in_full_norm_request = (uu___145_1555.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___145_1555.weakly_reduce_scrutinee)
          }
      | CompressUvars  ->
          let uu___146_1556 = fs  in
          {
            beta = (uu___146_1556.beta);
            iota = (uu___146_1556.iota);
            zeta = (uu___146_1556.zeta);
            weak = (uu___146_1556.weak);
            hnf = (uu___146_1556.hnf);
            primops = (uu___146_1556.primops);
            do_not_unfold_pure_lets = (uu___146_1556.do_not_unfold_pure_lets);
            unfold_until = (uu___146_1556.unfold_until);
            unfold_only = (uu___146_1556.unfold_only);
            unfold_fully = (uu___146_1556.unfold_fully);
            unfold_attr = (uu___146_1556.unfold_attr);
            unfold_tac = (uu___146_1556.unfold_tac);
            pure_subterms_within_computations =
              (uu___146_1556.pure_subterms_within_computations);
            simplify = (uu___146_1556.simplify);
            erase_universes = (uu___146_1556.erase_universes);
            allow_unbound_universes = (uu___146_1556.allow_unbound_universes);
            reify_ = (uu___146_1556.reify_);
            compress_uvars = true;
            no_full_norm = (uu___146_1556.no_full_norm);
            check_no_uvars = (uu___146_1556.check_no_uvars);
            unmeta = (uu___146_1556.unmeta);
            unascribe = (uu___146_1556.unascribe);
            in_full_norm_request = (uu___146_1556.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___146_1556.weakly_reduce_scrutinee)
          }
      | NoFullNorm  ->
          let uu___147_1557 = fs  in
          {
            beta = (uu___147_1557.beta);
            iota = (uu___147_1557.iota);
            zeta = (uu___147_1557.zeta);
            weak = (uu___147_1557.weak);
            hnf = (uu___147_1557.hnf);
            primops = (uu___147_1557.primops);
            do_not_unfold_pure_lets = (uu___147_1557.do_not_unfold_pure_lets);
            unfold_until = (uu___147_1557.unfold_until);
            unfold_only = (uu___147_1557.unfold_only);
            unfold_fully = (uu___147_1557.unfold_fully);
            unfold_attr = (uu___147_1557.unfold_attr);
            unfold_tac = (uu___147_1557.unfold_tac);
            pure_subterms_within_computations =
              (uu___147_1557.pure_subterms_within_computations);
            simplify = (uu___147_1557.simplify);
            erase_universes = (uu___147_1557.erase_universes);
            allow_unbound_universes = (uu___147_1557.allow_unbound_universes);
            reify_ = (uu___147_1557.reify_);
            compress_uvars = (uu___147_1557.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___147_1557.check_no_uvars);
            unmeta = (uu___147_1557.unmeta);
            unascribe = (uu___147_1557.unascribe);
            in_full_norm_request = (uu___147_1557.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___147_1557.weakly_reduce_scrutinee)
          }
      | CheckNoUvars  ->
          let uu___148_1558 = fs  in
          {
            beta = (uu___148_1558.beta);
            iota = (uu___148_1558.iota);
            zeta = (uu___148_1558.zeta);
            weak = (uu___148_1558.weak);
            hnf = (uu___148_1558.hnf);
            primops = (uu___148_1558.primops);
            do_not_unfold_pure_lets = (uu___148_1558.do_not_unfold_pure_lets);
            unfold_until = (uu___148_1558.unfold_until);
            unfold_only = (uu___148_1558.unfold_only);
            unfold_fully = (uu___148_1558.unfold_fully);
            unfold_attr = (uu___148_1558.unfold_attr);
            unfold_tac = (uu___148_1558.unfold_tac);
            pure_subterms_within_computations =
              (uu___148_1558.pure_subterms_within_computations);
            simplify = (uu___148_1558.simplify);
            erase_universes = (uu___148_1558.erase_universes);
            allow_unbound_universes = (uu___148_1558.allow_unbound_universes);
            reify_ = (uu___148_1558.reify_);
            compress_uvars = (uu___148_1558.compress_uvars);
            no_full_norm = (uu___148_1558.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___148_1558.unmeta);
            unascribe = (uu___148_1558.unascribe);
            in_full_norm_request = (uu___148_1558.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___148_1558.weakly_reduce_scrutinee)
          }
      | Unmeta  ->
          let uu___149_1559 = fs  in
          {
            beta = (uu___149_1559.beta);
            iota = (uu___149_1559.iota);
            zeta = (uu___149_1559.zeta);
            weak = (uu___149_1559.weak);
            hnf = (uu___149_1559.hnf);
            primops = (uu___149_1559.primops);
            do_not_unfold_pure_lets = (uu___149_1559.do_not_unfold_pure_lets);
            unfold_until = (uu___149_1559.unfold_until);
            unfold_only = (uu___149_1559.unfold_only);
            unfold_fully = (uu___149_1559.unfold_fully);
            unfold_attr = (uu___149_1559.unfold_attr);
            unfold_tac = (uu___149_1559.unfold_tac);
            pure_subterms_within_computations =
              (uu___149_1559.pure_subterms_within_computations);
            simplify = (uu___149_1559.simplify);
            erase_universes = (uu___149_1559.erase_universes);
            allow_unbound_universes = (uu___149_1559.allow_unbound_universes);
            reify_ = (uu___149_1559.reify_);
            compress_uvars = (uu___149_1559.compress_uvars);
            no_full_norm = (uu___149_1559.no_full_norm);
            check_no_uvars = (uu___149_1559.check_no_uvars);
            unmeta = true;
            unascribe = (uu___149_1559.unascribe);
            in_full_norm_request = (uu___149_1559.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___149_1559.weakly_reduce_scrutinee)
          }
      | Unascribe  ->
          let uu___150_1560 = fs  in
          {
            beta = (uu___150_1560.beta);
            iota = (uu___150_1560.iota);
            zeta = (uu___150_1560.zeta);
            weak = (uu___150_1560.weak);
            hnf = (uu___150_1560.hnf);
            primops = (uu___150_1560.primops);
            do_not_unfold_pure_lets = (uu___150_1560.do_not_unfold_pure_lets);
            unfold_until = (uu___150_1560.unfold_until);
            unfold_only = (uu___150_1560.unfold_only);
            unfold_fully = (uu___150_1560.unfold_fully);
            unfold_attr = (uu___150_1560.unfold_attr);
            unfold_tac = (uu___150_1560.unfold_tac);
            pure_subterms_within_computations =
              (uu___150_1560.pure_subterms_within_computations);
            simplify = (uu___150_1560.simplify);
            erase_universes = (uu___150_1560.erase_universes);
            allow_unbound_universes = (uu___150_1560.allow_unbound_universes);
            reify_ = (uu___150_1560.reify_);
            compress_uvars = (uu___150_1560.compress_uvars);
            no_full_norm = (uu___150_1560.no_full_norm);
            check_no_uvars = (uu___150_1560.check_no_uvars);
            unmeta = (uu___150_1560.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___150_1560.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___150_1560.weakly_reduce_scrutinee)
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
  fun uu___108_3222  ->
    match uu___108_3222 with
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
  fun uu___109_3284  ->
    match uu___109_3284 with
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
  fun uu___110_3404  ->
    match uu___110_3404 with | [] -> true | uu____3407 -> false
  
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
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3956 ->
                           let uu____3971 =
                             let uu____3972 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____3973 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____3972 uu____3973
                              in
                           failwith uu____3971
                       | uu____3976 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___111_4013  ->
                                         match uu___111_4013 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____4020 =
                                               let uu____4027 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____4027)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____4020
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___155_4037 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___155_4037.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___155_4037.FStar_Syntax_Syntax.sort)
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
                                              | uu____4042 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____4045 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___156_4049 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___156_4049.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___156_4049.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____4076 =
                        let uu____4077 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____4077  in
                      mk uu____4076 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____4085 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____4085  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____4087 = lookup_bvar env x  in
                    (match uu____4087 with
                     | Univ uu____4090 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___157_4094 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___157_4094.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___157_4094.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____4100,uu____4101) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4186  ->
                              fun stack1  ->
                                match uu____4186 with
                                | (a,aq) ->
                                    let uu____4198 =
                                      let uu____4199 =
                                        let uu____4206 =
                                          let uu____4207 =
                                            let uu____4238 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4238, false)  in
                                          Clos uu____4207  in
                                        (uu____4206, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4199  in
                                    uu____4198 :: stack1) args)
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
                    let uu____4414 = close_binders cfg env bs  in
                    (match uu____4414 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4461 =
                      let uu____4472 =
                        let uu____4479 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4479]  in
                      close_binders cfg env uu____4472  in
                    (match uu____4461 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4502 =
                             let uu____4503 =
                               let uu____4510 =
                                 let uu____4511 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4511
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4510, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4503  in
                           mk uu____4502 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4602 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4602
                      | FStar_Util.Inr c ->
                          let uu____4616 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4616
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4635 =
                        let uu____4636 =
                          let uu____4663 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4663, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4636  in
                      mk uu____4635 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4709 =
                            let uu____4710 =
                              let uu____4717 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4717, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4710  in
                          mk uu____4709 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4769  -> dummy :: env1) env
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
                    let uu____4790 =
                      let uu____4801 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4801
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4820 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___158_4836 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___158_4836.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___158_4836.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4820))
                       in
                    (match uu____4790 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___159_4854 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___159_4854.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___159_4854.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___159_4854.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___159_4854.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4868,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4931  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4948 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4948
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4960  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4984 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4984
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___160_4992 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___160_4992.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___160_4992.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___161_4993 = lb  in
                      let uu____4994 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___161_4993.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___161_4993.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4994;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___161_4993.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___161_4993.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____5026  -> fun env1  -> dummy :: env1)
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
            (fun uu____5115  ->
               let uu____5116 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5117 = env_to_string env  in
               let uu____5118 = stack_to_string stack  in
               let uu____5119 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5116 uu____5117 uu____5118 uu____5119);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5124,uu____5125),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5202 = close_binders cfg env' bs  in
               (match uu____5202 with
                | (bs1,uu____5216) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5232 =
                      let uu___162_5235 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___162_5235.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___162_5235.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5232)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5291 =
                 match uu____5291 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5406 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5435 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5519  ->
                                     fun uu____5520  ->
                                       match (uu____5519, uu____5520) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5659 = norm_pat env4 p1
                                              in
                                           (match uu____5659 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5435 with
                            | (pats1,env4) ->
                                ((let uu___163_5821 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___163_5821.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___164_5840 = x  in
                             let uu____5841 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___164_5840.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___164_5840.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5841
                             }  in
                           ((let uu___165_5855 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___165_5855.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___166_5866 = x  in
                             let uu____5867 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___166_5866.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___166_5866.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5867
                             }  in
                           ((let uu___167_5881 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___167_5881.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___168_5897 = x  in
                             let uu____5898 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___168_5897.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___168_5897.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5898
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___169_5915 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___169_5915.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5920 = norm_pat env2 pat  in
                     (match uu____5920 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____5989 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____5989
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____6008 =
                   let uu____6009 =
                     let uu____6032 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____6032)  in
                   FStar_Syntax_Syntax.Tm_match uu____6009  in
                 mk uu____6008 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____6145 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____6234  ->
                                       match uu____6234 with
                                       | (a,q) ->
                                           let uu____6253 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____6253, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____6145
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____6264 =
                       let uu____6271 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____6271)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____6264
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____6283 =
                       let uu____6292 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____6292)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____6283
                 | uu____6297 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____6303 -> failwith "Impossible: unexpected stack element")

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
        let uu____6317 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6390  ->
                  fun uu____6391  ->
                    match (uu____6390, uu____6391) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___170_6509 = b  in
                          let uu____6510 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___170_6509.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___170_6509.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6510
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____6317 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____6627 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6640 = inline_closure_env cfg env [] t  in
                 let uu____6641 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6640 uu____6641
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6654 = inline_closure_env cfg env [] t  in
                 let uu____6655 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6654 uu____6655
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6699  ->
                           match uu____6699 with
                           | (a,q) ->
                               let uu____6712 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6712, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___112_6727  ->
                           match uu___112_6727 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6731 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6731
                           | f -> f))
                    in
                 let uu____6735 =
                   let uu___171_6736 = c1  in
                   let uu____6737 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6737;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___171_6736.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6735)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___113_6747  ->
            match uu___113_6747 with
            | FStar_Syntax_Syntax.DECREASES uu____6748 -> false
            | uu____6751 -> true))

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
                   (fun uu___114_6769  ->
                      match uu___114_6769 with
                      | FStar_Syntax_Syntax.DECREASES uu____6770 -> false
                      | uu____6773 -> true))
               in
            let rc1 =
              let uu___172_6775 = rc  in
              let uu____6776 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___172_6775.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6776;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6785 -> lopt

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
    let uu____6890 =
      let uu____6899 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6899  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6890  in
  let arg_as_bounded_int uu____6925 =
    match uu____6925 with
    | (a,uu____6937) ->
        let uu____6944 =
          let uu____6945 = FStar_Syntax_Subst.compress a  in
          uu____6945.FStar_Syntax_Syntax.n  in
        (match uu____6944 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6955;
                FStar_Syntax_Syntax.vars = uu____6956;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6958;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6959;_},uu____6960)::[])
             when
             let uu____6999 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6999 "int_to_t" ->
             let uu____7000 =
               let uu____7005 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____7005)  in
             FStar_Pervasives_Native.Some uu____7000
         | uu____7010 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____7058 = f a  in FStar_Pervasives_Native.Some uu____7058
    | uu____7059 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____7115 = f a0 a1  in FStar_Pervasives_Native.Some uu____7115
    | uu____7116 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____7174 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____7174  in
  let binary_op as_a f res args =
    let uu____7245 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____7245  in
  let as_primitive_step is_strong uu____7282 =
    match uu____7282 with
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
           let uu____7342 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____7342)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7378 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____7378)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____7407 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____7407)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7443 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7443)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7479 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7479)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7611 =
          let uu____7620 = as_a a  in
          let uu____7623 = as_b b  in (uu____7620, uu____7623)  in
        (match uu____7611 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7638 =
               let uu____7639 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7639  in
             FStar_Pervasives_Native.Some uu____7638
         | uu____7640 -> FStar_Pervasives_Native.None)
    | uu____7649 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7669 =
        let uu____7670 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7670  in
      mk uu____7669 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7682 =
      let uu____7685 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7685  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7682  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7727 =
      let uu____7728 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7728  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7727
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7792 = arg_as_string a1  in
        (match uu____7792 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7798 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7798 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7811 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7811
              | uu____7812 -> FStar_Pervasives_Native.None)
         | uu____7817 -> FStar_Pervasives_Native.None)
    | uu____7820 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7840 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7840
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7877 =
          let uu____7898 = arg_as_string fn  in
          let uu____7901 = arg_as_int from_line  in
          let uu____7904 = arg_as_int from_col  in
          let uu____7907 = arg_as_int to_line  in
          let uu____7910 = arg_as_int to_col  in
          (uu____7898, uu____7901, uu____7904, uu____7907, uu____7910)  in
        (match uu____7877 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7941 =
                 let uu____7942 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7943 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7942 uu____7943  in
               let uu____7944 =
                 let uu____7945 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7946 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7945 uu____7946  in
               FStar_Range.mk_range fn1 uu____7941 uu____7944  in
             let uu____7947 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7947
         | uu____7948 -> FStar_Pervasives_Native.None)
    | uu____7969 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____8002)::(a1,uu____8004)::(a2,uu____8006)::[] ->
        let uu____8043 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8043 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____8048 -> FStar_Pervasives_Native.None)
    | uu____8049 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____8080)::[] ->
        let uu____8089 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____8089 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8095 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____8095
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8096 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____8122 =
      let uu____8139 =
        let uu____8156 =
          let uu____8173 =
            let uu____8190 =
              let uu____8207 =
                let uu____8224 =
                  let uu____8241 =
                    let uu____8258 =
                      let uu____8275 =
                        let uu____8292 =
                          let uu____8309 =
                            let uu____8326 =
                              let uu____8343 =
                                let uu____8360 =
                                  let uu____8377 =
                                    let uu____8394 =
                                      let uu____8411 =
                                        let uu____8428 =
                                          let uu____8445 =
                                            let uu____8462 =
                                              let uu____8479 =
                                                let uu____8494 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8494,
                                                  (Prims.parse_int "1"),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8503 =
                                                let uu____8520 =
                                                  let uu____8535 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8535,
                                                    (Prims.parse_int "1"),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8548 =
                                                  let uu____8565 =
                                                    let uu____8580 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8580,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____8589 =
                                                    let uu____8606 =
                                                      let uu____8621 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8621,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____8606]  in
                                                  uu____8565 :: uu____8589
                                                   in
                                                uu____8520 :: uu____8548  in
                                              uu____8479 :: uu____8503  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____8462
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____8445
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____8428
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____8411
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____8394
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8841 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8841 y)))
                                    :: uu____8377
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____8360
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____8343
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____8326
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____8309
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____8292
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____8275
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____9036 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____9036)))
                      :: uu____8258
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____9066 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____9066)))
                    :: uu____8241
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____9096 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____9096)))
                  :: uu____8224
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____9126 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____9126)))
                :: uu____8207
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____8190
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____8173
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____8156
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____8139
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____8122
     in
  let weak_ops =
    let uu____9281 =
      let uu____9296 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____9296, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____9281]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____9376 =
        let uu____9381 =
          let uu____9382 = FStar_Syntax_Syntax.as_arg c  in [uu____9382]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9381  in
      uu____9376 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9456 =
                let uu____9471 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9471, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9493  ->
                          fun uu____9494  ->
                            match (uu____9493, uu____9494) with
                            | ((int_to_t1,x),(uu____9513,y)) ->
                                let uu____9523 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9523)))
                 in
              let uu____9524 =
                let uu____9541 =
                  let uu____9556 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9556, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9578  ->
                            fun uu____9579  ->
                              match (uu____9578, uu____9579) with
                              | ((int_to_t1,x),(uu____9598,y)) ->
                                  let uu____9608 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9608)))
                   in
                let uu____9609 =
                  let uu____9626 =
                    let uu____9641 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9641, (Prims.parse_int "2"),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9663  ->
                              fun uu____9664  ->
                                match (uu____9663, uu____9664) with
                                | ((int_to_t1,x),(uu____9683,y)) ->
                                    let uu____9693 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9693)))
                     in
                  let uu____9694 =
                    let uu____9711 =
                      let uu____9726 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9726, (Prims.parse_int "1"),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9744  ->
                                match uu____9744 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9711]  in
                  uu____9626 :: uu____9694  in
                uu____9541 :: uu____9609  in
              uu____9456 :: uu____9524))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9874 =
                let uu____9889 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9889, (Prims.parse_int "2"),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9911  ->
                          fun uu____9912  ->
                            match (uu____9911, uu____9912) with
                            | ((int_to_t1,x),(uu____9931,y)) ->
                                let uu____9941 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9941)))
                 in
              let uu____9942 =
                let uu____9959 =
                  let uu____9974 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9974, (Prims.parse_int "2"),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9996  ->
                            fun uu____9997  ->
                              match (uu____9996, uu____9997) with
                              | ((int_to_t1,x),(uu____10016,y)) ->
                                  let uu____10026 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____10026)))
                   in
                [uu____9959]  in
              uu____9874 :: uu____9942))
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
    | (_typ,uu____10156)::(a1,uu____10158)::(a2,uu____10160)::[] ->
        let uu____10197 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10197 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___173_10201 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___173_10201.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___173_10201.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___174_10203 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___174_10203.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___174_10203.FStar_Syntax_Syntax.vars)
                })
         | uu____10204 -> FStar_Pervasives_Native.None)
    | (_typ,uu____10206)::uu____10207::(a1,uu____10209)::(a2,uu____10211)::[]
        ->
        let uu____10260 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____10260 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___173_10264 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___173_10264.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___173_10264.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___174_10266 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___174_10266.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___174_10266.FStar_Syntax_Syntax.vars)
                })
         | uu____10267 -> FStar_Pervasives_Native.None)
    | uu____10268 -> failwith "Unexpected number of arguments"  in
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
    let uu____10322 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____10322 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____10374 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10374) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____10436  ->
           fun subst1  ->
             match uu____10436 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10477,uu____10478)) ->
                      let uu____10537 = b  in
                      (match uu____10537 with
                       | (bv,uu____10545) ->
                           let uu____10546 =
                             let uu____10547 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10547  in
                           if uu____10546
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10552 = unembed_binder term1  in
                              match uu____10552 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10559 =
                                      let uu___175_10560 = bv  in
                                      let uu____10561 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___175_10560.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___175_10560.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10561
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10559
                                     in
                                  let b_for_x =
                                    let uu____10565 =
                                      let uu____10572 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10572)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10565  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___115_10586  ->
                                         match uu___115_10586 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10587,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10589;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10590;_})
                                             ->
                                             let uu____10595 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10595
                                         | uu____10596 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10597 -> subst1)) env []
  
let reduce_primops :
  'Auu____10620 'Auu____10621 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10620) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10621 ->
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
            (let uu____10669 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10669 with
             | (head1,args) ->
                 let uu____10708 =
                   let uu____10709 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10709.FStar_Syntax_Syntax.n  in
                 (match uu____10708 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10715 = find_prim_step cfg fv  in
                      (match uu____10715 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10741  ->
                                   let uu____10742 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10743 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10750 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10742 uu____10743 uu____10750);
                              tm)
                           else
                             (let uu____10752 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10752 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10866  ->
                                        let uu____10867 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10867);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10870  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10872 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10872 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10880  ->
                                              let uu____10881 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10881);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10887  ->
                                              let uu____10888 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10889 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10888 uu____10889);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10890 ->
                           (log_primops cfg
                              (fun uu____10894  ->
                                 let uu____10895 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10895);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10899  ->
                            let uu____10900 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10900);
                       (match args with
                        | (a1,uu____10904)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10921 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10933  ->
                            let uu____10934 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10934);
                       (match args with
                        | (t,uu____10938)::(r,uu____10940)::[] ->
                            let uu____10967 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____10967 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___176_10973 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___176_10973.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___176_10973.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____10976 -> tm))
                  | uu____10985 -> tm))
  
let reduce_equality :
  'Auu____10996 'Auu____10997 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10996) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10997 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___177_11043 = cfg  in
         {
           steps =
             (let uu___178_11046 = default_steps  in
              {
                beta = (uu___178_11046.beta);
                iota = (uu___178_11046.iota);
                zeta = (uu___178_11046.zeta);
                weak = (uu___178_11046.weak);
                hnf = (uu___178_11046.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___178_11046.do_not_unfold_pure_lets);
                unfold_until = (uu___178_11046.unfold_until);
                unfold_only = (uu___178_11046.unfold_only);
                unfold_fully = (uu___178_11046.unfold_fully);
                unfold_attr = (uu___178_11046.unfold_attr);
                unfold_tac = (uu___178_11046.unfold_tac);
                pure_subterms_within_computations =
                  (uu___178_11046.pure_subterms_within_computations);
                simplify = (uu___178_11046.simplify);
                erase_universes = (uu___178_11046.erase_universes);
                allow_unbound_universes =
                  (uu___178_11046.allow_unbound_universes);
                reify_ = (uu___178_11046.reify_);
                compress_uvars = (uu___178_11046.compress_uvars);
                no_full_norm = (uu___178_11046.no_full_norm);
                check_no_uvars = (uu___178_11046.check_no_uvars);
                unmeta = (uu___178_11046.unmeta);
                unascribe = (uu___178_11046.unascribe);
                in_full_norm_request = (uu___178_11046.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___178_11046.weakly_reduce_scrutinee)
              });
           tcenv = (uu___177_11043.tcenv);
           debug = (uu___177_11043.debug);
           delta_level = (uu___177_11043.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___177_11043.strong);
           memoize_lazy = (uu___177_11043.memoize_lazy);
           normalize_pure_lets = (uu___177_11043.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____11053 .
    FStar_Syntax_Syntax.term -> 'Auu____11053 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____11068 =
        let uu____11075 =
          let uu____11076 = FStar_Syntax_Util.un_uinst hd1  in
          uu____11076.FStar_Syntax_Syntax.n  in
        (uu____11075, args)  in
      match uu____11068 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11082::uu____11083::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____11087::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____11092::uu____11093::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____11096 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___116_11109  ->
    match uu___116_11109 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____11115 =
          let uu____11118 =
            let uu____11119 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____11119  in
          [uu____11118]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11115
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____11125 =
          let uu____11128 =
            let uu____11129 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____11129  in
          [uu____11128]  in
        (UnfoldUntil FStar_Syntax_Syntax.delta_constant) :: uu____11125
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____11150 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____11150) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____11196 =
          let uu____11201 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____11201 s  in
        match uu____11196 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____11217 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____11217
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____11234::(tm,uu____11236)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____11265)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____11286)::uu____11287::(tm,uu____11289)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____11330 =
            let uu____11335 = full_norm steps  in parse_steps uu____11335  in
          (match uu____11330 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____11374 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___117_11393  ->
    match uu___117_11393 with
    | (App
        (uu____11396,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____11397;
                       FStar_Syntax_Syntax.vars = uu____11398;_},uu____11399,uu____11400))::uu____11401
        -> true
    | uu____11406 -> false
  
let firstn :
  'Auu____11415 .
    Prims.int ->
      'Auu____11415 Prims.list ->
        ('Auu____11415 Prims.list,'Auu____11415 Prims.list)
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
          (uu____11457,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____11458;
                         FStar_Syntax_Syntax.vars = uu____11459;_},uu____11460,uu____11461))::uu____11462
          -> (cfg.steps).reify_
      | uu____11467 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11490) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11500) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11519  ->
                  match uu____11519 with
                  | (a,uu____11527) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11533 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11558 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11559 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11574 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11575 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11576 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11577 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11578 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11579 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11586 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11593 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11606 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11623 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11636 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11643 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11705  ->
                   match uu____11705 with
                   | (a,uu____11713) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11720) ->
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
                     (fun uu____11842  ->
                        match uu____11842 with
                        | (a,uu____11850) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11855,uu____11856,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11862,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11868 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11875 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11876 -> false))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____12168 ->
                   let uu____12193 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____12193
               | uu____12194 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____12202  ->
               let uu____12203 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____12204 = FStar_Syntax_Print.term_to_string t1  in
               let uu____12205 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____12212 =
                 let uu____12213 =
                   let uu____12216 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____12216
                    in
                 stack_to_string uu____12213  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____12203 uu____12204 uu____12205 uu____12212);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____12239 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____12240 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____12241 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12242;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_18;
                 FStar_Syntax_Syntax.fv_qual = uu____12243;_}
               when _0_18 = (Prims.parse_int "0") -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12246;
                 FStar_Syntax_Syntax.fv_delta = uu____12247;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____12248;
                 FStar_Syntax_Syntax.fv_delta = uu____12249;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____12250);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____12257 ->
               let uu____12264 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____12264
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____12294 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____12294)
               ->
               let cfg' =
                 let uu___179_12296 = cfg  in
                 {
                   steps =
                     (let uu___180_12299 = cfg.steps  in
                      {
                        beta = (uu___180_12299.beta);
                        iota = (uu___180_12299.iota);
                        zeta = (uu___180_12299.zeta);
                        weak = (uu___180_12299.weak);
                        hnf = (uu___180_12299.hnf);
                        primops = (uu___180_12299.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___180_12299.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___180_12299.unfold_attr);
                        unfold_tac = (uu___180_12299.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___180_12299.pure_subterms_within_computations);
                        simplify = (uu___180_12299.simplify);
                        erase_universes = (uu___180_12299.erase_universes);
                        allow_unbound_universes =
                          (uu___180_12299.allow_unbound_universes);
                        reify_ = (uu___180_12299.reify_);
                        compress_uvars = (uu___180_12299.compress_uvars);
                        no_full_norm = (uu___180_12299.no_full_norm);
                        check_no_uvars = (uu___180_12299.check_no_uvars);
                        unmeta = (uu___180_12299.unmeta);
                        unascribe = (uu___180_12299.unascribe);
                        in_full_norm_request =
                          (uu___180_12299.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___180_12299.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___179_12296.tcenv);
                   debug = (uu___179_12296.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant];
                   primitive_steps = (uu___179_12296.primitive_steps);
                   strong = (uu___179_12296.strong);
                   memoize_lazy = (uu___179_12296.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____12304 = get_norm_request (norm cfg' env []) args  in
               (match uu____12304 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____12333  ->
                              fun stack1  ->
                                match uu____12333 with
                                | (a,aq) ->
                                    let uu____12345 =
                                      let uu____12346 =
                                        let uu____12353 =
                                          let uu____12354 =
                                            let uu____12385 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____12385, false)  in
                                          Clos uu____12354  in
                                        (uu____12353, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____12346  in
                                    uu____12345 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____12473  ->
                          let uu____12474 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12474);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____12496 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___118_12501  ->
                                match uu___118_12501 with
                                | UnfoldUntil uu____12502 -> true
                                | UnfoldOnly uu____12503 -> true
                                | UnfoldFully uu____12506 -> true
                                | uu____12509 -> false))
                         in
                      if uu____12496
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___181_12514 = cfg  in
                      let uu____12515 =
                        let uu___182_12516 = to_fsteps s  in
                        {
                          beta = (uu___182_12516.beta);
                          iota = (uu___182_12516.iota);
                          zeta = (uu___182_12516.zeta);
                          weak = (uu___182_12516.weak);
                          hnf = (uu___182_12516.hnf);
                          primops = (uu___182_12516.primops);
                          do_not_unfold_pure_lets =
                            (uu___182_12516.do_not_unfold_pure_lets);
                          unfold_until = (uu___182_12516.unfold_until);
                          unfold_only = (uu___182_12516.unfold_only);
                          unfold_fully = (uu___182_12516.unfold_fully);
                          unfold_attr = (uu___182_12516.unfold_attr);
                          unfold_tac = (uu___182_12516.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___182_12516.pure_subterms_within_computations);
                          simplify = (uu___182_12516.simplify);
                          erase_universes = (uu___182_12516.erase_universes);
                          allow_unbound_universes =
                            (uu___182_12516.allow_unbound_universes);
                          reify_ = (uu___182_12516.reify_);
                          compress_uvars = (uu___182_12516.compress_uvars);
                          no_full_norm = (uu___182_12516.no_full_norm);
                          check_no_uvars = (uu___182_12516.check_no_uvars);
                          unmeta = (uu___182_12516.unmeta);
                          unascribe = (uu___182_12516.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___182_12516.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____12515;
                        tcenv = (uu___181_12514.tcenv);
                        debug = (uu___181_12514.debug);
                        delta_level;
                        primitive_steps = (uu___181_12514.primitive_steps);
                        strong = (uu___181_12514.strong);
                        memoize_lazy = (uu___181_12514.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12525 =
                          let uu____12526 =
                            let uu____12531 = FStar_Util.now ()  in
                            (t1, uu____12531)  in
                          Debug uu____12526  in
                        uu____12525 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12535 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12535
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12544 =
                      let uu____12551 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12551, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12544  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12561 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12561  in
               let uu____12562 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____12562
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____12568  ->
                       let uu____12569 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12570 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12569 uu____12570);
                  if b
                  then
                    (let uu____12571 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____12571 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____12579 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____12579) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____12592),uu____12593);
                                FStar_Syntax_Syntax.sigrng = uu____12594;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____12596;
                                FStar_Syntax_Syntax.sigattrs = uu____12597;_},uu____12598),uu____12599)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____12658 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___119_12662  ->
                               match uu___119_12662 with
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
                          (let uu____12672 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____12672))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____12691) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____12726,uu____12727) -> false)))
                     in
                  let uu____12744 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____12760 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____12760 then (true, true) else (false, false)
                     in
                  match uu____12744 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____12773  ->
                            let uu____12774 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____12775 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____12776 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____12774 uu____12775 uu____12776);
                       if should_delta2
                       then
                         (let uu____12777 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___183_12787 = cfg  in
                                 {
                                   steps =
                                     (let uu___184_12790 = cfg.steps  in
                                      {
                                        beta = (uu___184_12790.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___184_12790.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___184_12790.unfold_attr);
                                        unfold_tac =
                                          (uu___184_12790.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___184_12790.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___184_12790.erase_universes);
                                        allow_unbound_universes =
                                          (uu___184_12790.allow_unbound_universes);
                                        reify_ = (uu___184_12790.reify_);
                                        compress_uvars =
                                          (uu___184_12790.compress_uvars);
                                        no_full_norm =
                                          (uu___184_12790.no_full_norm);
                                        check_no_uvars =
                                          (uu___184_12790.check_no_uvars);
                                        unmeta = (uu___184_12790.unmeta);
                                        unascribe =
                                          (uu___184_12790.unascribe);
                                        in_full_norm_request =
                                          (uu___184_12790.in_full_norm_request);
                                        weakly_reduce_scrutinee =
                                          (uu___184_12790.weakly_reduce_scrutinee)
                                      });
                                   tcenv = (uu___183_12787.tcenv);
                                   debug = (uu___183_12787.debug);
                                   delta_level = (uu___183_12787.delta_level);
                                   primitive_steps =
                                     (uu___183_12787.primitive_steps);
                                   strong = (uu___183_12787.strong);
                                   memoize_lazy =
                                     (uu___183_12787.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___183_12787.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____12777 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12800 = lookup_bvar env x  in
               (match uu____12800 with
                | Univ uu____12801 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12850 = FStar_ST.op_Bang r  in
                      (match uu____12850 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12972  ->
                                 let uu____12973 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12974 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12973
                                   uu____12974);
                            (let uu____12975 = maybe_weakly_reduced t'  in
                             if uu____12975
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____12976 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____13047)::uu____13048 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____13057)::uu____13058 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____13070,uu____13071))::stack_rest ->
                    (match c with
                     | Univ uu____13075 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____13084 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____13105  ->
                                    let uu____13106 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13106);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____13134  ->
                                    let uu____13135 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____13135);
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
                       (fun uu____13201  ->
                          let uu____13202 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____13202);
                     norm cfg env stack1 t1)
                | (Debug uu____13203)::uu____13204 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___185_13214 = cfg.steps  in
                             {
                               beta = (uu___185_13214.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___185_13214.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___185_13214.unfold_until);
                               unfold_only = (uu___185_13214.unfold_only);
                               unfold_fully = (uu___185_13214.unfold_fully);
                               unfold_attr = (uu___185_13214.unfold_attr);
                               unfold_tac = (uu___185_13214.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___185_13214.erase_universes);
                               allow_unbound_universes =
                                 (uu___185_13214.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___185_13214.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___185_13214.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___185_13214.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___185_13214.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___186_13216 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___186_13216.tcenv);
                               debug = (uu___186_13216.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___186_13216.primitive_steps);
                               strong = (uu___186_13216.strong);
                               memoize_lazy = (uu___186_13216.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___186_13216.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13218 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13218 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13250  -> dummy :: env1) env)
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
                                          let uu____13291 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13291)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_13296 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_13296.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_13296.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13297 -> lopt  in
                           (log cfg
                              (fun uu____13303  ->
                                 let uu____13304 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13304);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___188_13313 = cfg  in
                               {
                                 steps = (uu___188_13313.steps);
                                 tcenv = (uu___188_13313.tcenv);
                                 debug = (uu___188_13313.debug);
                                 delta_level = (uu___188_13313.delta_level);
                                 primitive_steps =
                                   (uu___188_13313.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___188_13313.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___188_13313.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____13316)::uu____13317 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___185_13329 = cfg.steps  in
                             {
                               beta = (uu___185_13329.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___185_13329.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___185_13329.unfold_until);
                               unfold_only = (uu___185_13329.unfold_only);
                               unfold_fully = (uu___185_13329.unfold_fully);
                               unfold_attr = (uu___185_13329.unfold_attr);
                               unfold_tac = (uu___185_13329.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___185_13329.erase_universes);
                               allow_unbound_universes =
                                 (uu___185_13329.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___185_13329.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___185_13329.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___185_13329.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___185_13329.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___186_13331 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___186_13331.tcenv);
                               debug = (uu___186_13331.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___186_13331.primitive_steps);
                               strong = (uu___186_13331.strong);
                               memoize_lazy = (uu___186_13331.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___186_13331.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13333 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13333 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13365  -> dummy :: env1) env)
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
                                          let uu____13406 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13406)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_13411 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_13411.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_13411.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13412 -> lopt  in
                           (log cfg
                              (fun uu____13418  ->
                                 let uu____13419 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13419);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___188_13428 = cfg  in
                               {
                                 steps = (uu___188_13428.steps);
                                 tcenv = (uu___188_13428.tcenv);
                                 debug = (uu___188_13428.debug);
                                 delta_level = (uu___188_13428.delta_level);
                                 primitive_steps =
                                   (uu___188_13428.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___188_13428.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___188_13428.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13431)::uu____13432 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___185_13446 = cfg.steps  in
                             {
                               beta = (uu___185_13446.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___185_13446.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___185_13446.unfold_until);
                               unfold_only = (uu___185_13446.unfold_only);
                               unfold_fully = (uu___185_13446.unfold_fully);
                               unfold_attr = (uu___185_13446.unfold_attr);
                               unfold_tac = (uu___185_13446.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___185_13446.erase_universes);
                               allow_unbound_universes =
                                 (uu___185_13446.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___185_13446.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___185_13446.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___185_13446.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___185_13446.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___186_13448 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___186_13448.tcenv);
                               debug = (uu___186_13448.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___186_13448.primitive_steps);
                               strong = (uu___186_13448.strong);
                               memoize_lazy = (uu___186_13448.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___186_13448.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13450 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13450 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13482  -> dummy :: env1) env)
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
                                          let uu____13523 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13523)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_13528 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_13528.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_13528.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13529 -> lopt  in
                           (log cfg
                              (fun uu____13535  ->
                                 let uu____13536 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13536);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___188_13545 = cfg  in
                               {
                                 steps = (uu___188_13545.steps);
                                 tcenv = (uu___188_13545.tcenv);
                                 debug = (uu___188_13545.debug);
                                 delta_level = (uu___188_13545.delta_level);
                                 primitive_steps =
                                   (uu___188_13545.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___188_13545.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___188_13545.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13548)::uu____13549 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___185_13563 = cfg.steps  in
                             {
                               beta = (uu___185_13563.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___185_13563.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___185_13563.unfold_until);
                               unfold_only = (uu___185_13563.unfold_only);
                               unfold_fully = (uu___185_13563.unfold_fully);
                               unfold_attr = (uu___185_13563.unfold_attr);
                               unfold_tac = (uu___185_13563.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___185_13563.erase_universes);
                               allow_unbound_universes =
                                 (uu___185_13563.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___185_13563.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___185_13563.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___185_13563.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___185_13563.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___186_13565 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___186_13565.tcenv);
                               debug = (uu___186_13565.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___186_13565.primitive_steps);
                               strong = (uu___186_13565.strong);
                               memoize_lazy = (uu___186_13565.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___186_13565.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13567 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13567 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13599  -> dummy :: env1) env)
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
                                          let uu____13640 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13640)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_13645 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_13645.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_13645.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13646 -> lopt  in
                           (log cfg
                              (fun uu____13652  ->
                                 let uu____13653 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13653);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___188_13662 = cfg  in
                               {
                                 steps = (uu___188_13662.steps);
                                 tcenv = (uu___188_13662.tcenv);
                                 debug = (uu___188_13662.debug);
                                 delta_level = (uu___188_13662.delta_level);
                                 primitive_steps =
                                   (uu___188_13662.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___188_13662.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___188_13662.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13665)::uu____13666 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___185_13684 = cfg.steps  in
                             {
                               beta = (uu___185_13684.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___185_13684.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___185_13684.unfold_until);
                               unfold_only = (uu___185_13684.unfold_only);
                               unfold_fully = (uu___185_13684.unfold_fully);
                               unfold_attr = (uu___185_13684.unfold_attr);
                               unfold_tac = (uu___185_13684.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___185_13684.erase_universes);
                               allow_unbound_universes =
                                 (uu___185_13684.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___185_13684.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___185_13684.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___185_13684.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___185_13684.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___186_13686 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___186_13686.tcenv);
                               debug = (uu___186_13686.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___186_13686.primitive_steps);
                               strong = (uu___186_13686.strong);
                               memoize_lazy = (uu___186_13686.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___186_13686.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13688 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13688 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13720  -> dummy :: env1) env)
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
                                          let uu____13761 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13761)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_13766 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_13766.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_13766.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13767 -> lopt  in
                           (log cfg
                              (fun uu____13773  ->
                                 let uu____13774 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13774);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___188_13783 = cfg  in
                               {
                                 steps = (uu___188_13783.steps);
                                 tcenv = (uu___188_13783.tcenv);
                                 debug = (uu___188_13783.debug);
                                 delta_level = (uu___188_13783.delta_level);
                                 primitive_steps =
                                   (uu___188_13783.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___188_13783.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___188_13783.normalize_pure_lets)
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
                             let uu___185_13789 = cfg.steps  in
                             {
                               beta = (uu___185_13789.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___185_13789.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___185_13789.unfold_until);
                               unfold_only = (uu___185_13789.unfold_only);
                               unfold_fully = (uu___185_13789.unfold_fully);
                               unfold_attr = (uu___185_13789.unfold_attr);
                               unfold_tac = (uu___185_13789.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___185_13789.erase_universes);
                               allow_unbound_universes =
                                 (uu___185_13789.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___185_13789.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___185_13789.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___185_13789.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___185_13789.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___186_13791 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___186_13791.tcenv);
                               debug = (uu___186_13791.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___186_13791.primitive_steps);
                               strong = (uu___186_13791.strong);
                               memoize_lazy = (uu___186_13791.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___186_13791.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13793 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13793 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13825  -> dummy :: env1) env)
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
                                          let uu____13866 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13866)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___187_13871 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___187_13871.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___187_13871.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13872 -> lopt  in
                           (log cfg
                              (fun uu____13878  ->
                                 let uu____13879 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13879);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___188_13888 = cfg  in
                               {
                                 steps = (uu___188_13888.steps);
                                 tcenv = (uu___188_13888.tcenv);
                                 debug = (uu___188_13888.debug);
                                 delta_level = (uu___188_13888.delta_level);
                                 primitive_steps =
                                   (uu___188_13888.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___188_13888.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___188_13888.normalize_pure_lets)
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
                      (fun uu____13927  ->
                         fun stack1  ->
                           match uu____13927 with
                           | (a,aq) ->
                               let uu____13939 =
                                 let uu____13940 =
                                   let uu____13947 =
                                     let uu____13948 =
                                       let uu____13979 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____13979, false)  in
                                     Clos uu____13948  in
                                   (uu____13947, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____13940  in
                               uu____13939 :: stack1) args)
                  in
               (log cfg
                  (fun uu____14067  ->
                     let uu____14068 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____14068);
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
                             ((let uu___189_14114 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___189_14114.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___189_14114.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____14115 ->
                      let uu____14130 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14130)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____14133 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____14133 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____14158 =
                          let uu____14159 =
                            let uu____14166 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___190_14172 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___190_14172.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___190_14172.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____14166)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____14159  in
                        mk uu____14158 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____14191 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____14191
               else
                 (let uu____14193 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____14193 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____14201 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____14223  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____14201 c1  in
                      let t2 =
                        let uu____14245 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____14245 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____14356)::uu____14357 ->
                    (log cfg
                       (fun uu____14370  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14371)::uu____14372 ->
                    (log cfg
                       (fun uu____14383  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14384,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14385;
                                   FStar_Syntax_Syntax.vars = uu____14386;_},uu____14387,uu____14388))::uu____14389
                    ->
                    (log cfg
                       (fun uu____14396  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14397)::uu____14398 ->
                    (log cfg
                       (fun uu____14409  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14410 ->
                    (log cfg
                       (fun uu____14413  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14417  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14442 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14442
                         | FStar_Util.Inr c ->
                             let uu____14452 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14452
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14471 =
                               let uu____14472 =
                                 let uu____14499 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14499, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14472
                                in
                             mk uu____14471 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14534 ->
                           let uu____14535 =
                             let uu____14536 =
                               let uu____14537 =
                                 let uu____14564 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14564, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14537
                                in
                             mk uu____14536 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14535))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 if
                   ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee)
                     && (Prims.op_Negation (cfg.steps).weak)
                 then
                   let uu___191_14641 = cfg  in
                   {
                     steps =
                       (let uu___192_14644 = cfg.steps  in
                        {
                          beta = (uu___192_14644.beta);
                          iota = (uu___192_14644.iota);
                          zeta = (uu___192_14644.zeta);
                          weak = true;
                          hnf = (uu___192_14644.hnf);
                          primops = (uu___192_14644.primops);
                          do_not_unfold_pure_lets =
                            (uu___192_14644.do_not_unfold_pure_lets);
                          unfold_until = (uu___192_14644.unfold_until);
                          unfold_only = (uu___192_14644.unfold_only);
                          unfold_fully = (uu___192_14644.unfold_fully);
                          unfold_attr = (uu___192_14644.unfold_attr);
                          unfold_tac = (uu___192_14644.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___192_14644.pure_subterms_within_computations);
                          simplify = (uu___192_14644.simplify);
                          erase_universes = (uu___192_14644.erase_universes);
                          allow_unbound_universes =
                            (uu___192_14644.allow_unbound_universes);
                          reify_ = (uu___192_14644.reify_);
                          compress_uvars = (uu___192_14644.compress_uvars);
                          no_full_norm = (uu___192_14644.no_full_norm);
                          check_no_uvars = (uu___192_14644.check_no_uvars);
                          unmeta = (uu___192_14644.unmeta);
                          unascribe = (uu___192_14644.unascribe);
                          in_full_norm_request =
                            (uu___192_14644.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___192_14644.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___191_14641.tcenv);
                     debug = (uu___191_14641.debug);
                     delta_level = (uu___191_14641.delta_level);
                     primitive_steps = (uu___191_14641.primitive_steps);
                     strong = (uu___191_14641.strong);
                     memoize_lazy = (uu___191_14641.memoize_lazy);
                     normalize_pure_lets =
                       (uu___191_14641.normalize_pure_lets)
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
                         let uu____14680 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14680 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___193_14700 = cfg  in
                               let uu____14701 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___193_14700.steps);
                                 tcenv = uu____14701;
                                 debug = (uu___193_14700.debug);
                                 delta_level = (uu___193_14700.delta_level);
                                 primitive_steps =
                                   (uu___193_14700.primitive_steps);
                                 strong = (uu___193_14700.strong);
                                 memoize_lazy = (uu___193_14700.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___193_14700.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14708 =
                                 let uu____14709 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14709  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14708
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___194_14712 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___194_14712.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___194_14712.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___194_14712.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___194_14712.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____14713 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14713
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14724,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14725;
                               FStar_Syntax_Syntax.lbunivs = uu____14726;
                               FStar_Syntax_Syntax.lbtyp = uu____14727;
                               FStar_Syntax_Syntax.lbeff = uu____14728;
                               FStar_Syntax_Syntax.lbdef = uu____14729;
                               FStar_Syntax_Syntax.lbattrs = uu____14730;
                               FStar_Syntax_Syntax.lbpos = uu____14731;_}::uu____14732),uu____14733)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14773 =
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
               if uu____14773
               then
                 let binder =
                   let uu____14775 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14775  in
                 let env1 =
                   let uu____14785 =
                     let uu____14792 =
                       let uu____14793 =
                         let uu____14824 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14824,
                           false)
                          in
                       Clos uu____14793  in
                     ((FStar_Pervasives_Native.Some binder), uu____14792)  in
                   uu____14785 :: env  in
                 (log cfg
                    (fun uu____14919  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____14923  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14924 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14924))
                 else
                   (let uu____14926 =
                      let uu____14931 =
                        let uu____14932 =
                          let uu____14937 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14937
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14932]  in
                      FStar_Syntax_Subst.open_term uu____14931 body  in
                    match uu____14926 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14958  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14966 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14966  in
                            FStar_Util.Inl
                              (let uu___195_14976 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___195_14976.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___195_14976.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____14979  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___196_14981 = lb  in
                             let uu____14982 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___196_14981.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___196_14981.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14982;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___196_14981.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___196_14981.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15007  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___197_15030 = cfg  in
                             {
                               steps = (uu___197_15030.steps);
                               tcenv = (uu___197_15030.tcenv);
                               debug = (uu___197_15030.debug);
                               delta_level = (uu___197_15030.delta_level);
                               primitive_steps =
                                 (uu___197_15030.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___197_15030.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___197_15030.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____15033  ->
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
               let uu____15050 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____15050 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____15086 =
                               let uu___198_15087 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___198_15087.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___198_15087.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____15086  in
                           let uu____15088 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____15088 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____15114 =
                                   FStar_List.map (fun uu____15130  -> dummy)
                                     lbs1
                                    in
                                 let uu____15131 =
                                   let uu____15140 =
                                     FStar_List.map
                                       (fun uu____15160  -> dummy) xs1
                                      in
                                   FStar_List.append uu____15140 env  in
                                 FStar_List.append uu____15114 uu____15131
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____15184 =
                                       let uu___199_15185 = rc  in
                                       let uu____15186 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___199_15185.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____15186;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___199_15185.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____15184
                                 | uu____15195 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___200_15201 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___200_15201.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___200_15201.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___200_15201.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___200_15201.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____15211 =
                        FStar_List.map (fun uu____15227  -> dummy) lbs2  in
                      FStar_List.append uu____15211 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____15235 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____15235 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___201_15251 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___201_15251.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___201_15251.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____15280 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____15280
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____15299 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____15375  ->
                        match uu____15375 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___202_15496 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___202_15496.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___202_15496.FStar_Syntax_Syntax.sort)
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
               (match uu____15299 with
                | (rec_env,memos,uu____15723) ->
                    let uu____15776 =
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
                             let uu____16099 =
                               let uu____16106 =
                                 let uu____16107 =
                                   let uu____16138 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____16138, false)
                                    in
                                 Clos uu____16107  in
                               (FStar_Pervasives_Native.None, uu____16106)
                                in
                             uu____16099 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____16242  ->
                     let uu____16243 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____16243);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____16265 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____16267::uu____16268 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____16273) ->
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
                             | uu____16296 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____16310 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____16310
                              | uu____16321 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____16327 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____16353 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____16369 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____16384 =
                        let uu____16385 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____16386 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____16385 uu____16386
                         in
                      failwith uu____16384
                    else
                      (let uu____16388 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____16388)
                | uu____16389 -> norm cfg env stack t2))

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
                let uu____16399 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____16399  in
              let uu____16400 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____16400 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16413  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16424  ->
                        let uu____16425 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16426 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16425 uu____16426);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____16431 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____16431 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____16440))::stack1 ->
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
                      | uu____16479 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____16482 ->
                          let uu____16485 =
                            let uu____16486 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16486
                             in
                          failwith uu____16485
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
                  let uu___203_16510 = cfg  in
                  let uu____16511 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____16511;
                    tcenv = (uu___203_16510.tcenv);
                    debug = (uu___203_16510.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___203_16510.primitive_steps);
                    strong = (uu___203_16510.strong);
                    memoize_lazy = (uu___203_16510.memoize_lazy);
                    normalize_pure_lets =
                      (uu___203_16510.normalize_pure_lets)
                  }
                else
                  (let uu___204_16513 = cfg  in
                   {
                     steps =
                       (let uu___205_16516 = cfg.steps  in
                        {
                          beta = (uu___205_16516.beta);
                          iota = (uu___205_16516.iota);
                          zeta = false;
                          weak = (uu___205_16516.weak);
                          hnf = (uu___205_16516.hnf);
                          primops = (uu___205_16516.primops);
                          do_not_unfold_pure_lets =
                            (uu___205_16516.do_not_unfold_pure_lets);
                          unfold_until = (uu___205_16516.unfold_until);
                          unfold_only = (uu___205_16516.unfold_only);
                          unfold_fully = (uu___205_16516.unfold_fully);
                          unfold_attr = (uu___205_16516.unfold_attr);
                          unfold_tac = (uu___205_16516.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___205_16516.pure_subterms_within_computations);
                          simplify = (uu___205_16516.simplify);
                          erase_universes = (uu___205_16516.erase_universes);
                          allow_unbound_universes =
                            (uu___205_16516.allow_unbound_universes);
                          reify_ = (uu___205_16516.reify_);
                          compress_uvars = (uu___205_16516.compress_uvars);
                          no_full_norm = (uu___205_16516.no_full_norm);
                          check_no_uvars = (uu___205_16516.check_no_uvars);
                          unmeta = (uu___205_16516.unmeta);
                          unascribe = (uu___205_16516.unascribe);
                          in_full_norm_request =
                            (uu___205_16516.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___205_16516.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___204_16513.tcenv);
                     debug = (uu___204_16513.debug);
                     delta_level = (uu___204_16513.delta_level);
                     primitive_steps = (uu___204_16513.primitive_steps);
                     strong = (uu___204_16513.strong);
                     memoize_lazy = (uu___204_16513.memoize_lazy);
                     normalize_pure_lets =
                       (uu___204_16513.normalize_pure_lets)
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
                  (fun uu____16550  ->
                     let uu____16551 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16552 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16551
                       uu____16552);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____16554 =
                   let uu____16555 = FStar_Syntax_Subst.compress head3  in
                   uu____16555.FStar_Syntax_Syntax.n  in
                 match uu____16554 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____16573 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16573
                        in
                     let uu____16574 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16574 with
                      | (uu____16575,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16585 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16595 =
                                   let uu____16596 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16596.FStar_Syntax_Syntax.n  in
                                 match uu____16595 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16602,uu____16603))
                                     ->
                                     let uu____16612 =
                                       let uu____16613 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16613.FStar_Syntax_Syntax.n  in
                                     (match uu____16612 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16619,msrc,uu____16621))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16630 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16630
                                      | uu____16631 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16632 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16633 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16633 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___206_16638 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___206_16638.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___206_16638.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___206_16638.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___206_16638.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___206_16638.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____16639 = FStar_List.tl stack  in
                                    let uu____16640 =
                                      let uu____16641 =
                                        let uu____16648 =
                                          let uu____16649 =
                                            let uu____16662 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16662)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16649
                                           in
                                        FStar_Syntax_Syntax.mk uu____16648
                                         in
                                      uu____16641
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16639 uu____16640
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16678 =
                                      let uu____16679 = is_return body  in
                                      match uu____16679 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16683;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16684;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16687 -> false  in
                                    if uu____16678
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
                                         let uu____16708 =
                                           let uu____16715 =
                                             let uu____16716 =
                                               let uu____16733 =
                                                 let uu____16740 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16740]  in
                                               (uu____16733, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16716
                                              in
                                           FStar_Syntax_Syntax.mk uu____16715
                                            in
                                         uu____16708
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16774 =
                                           let uu____16775 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16775.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16774 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16781::uu____16782::[])
                                             ->
                                             let uu____16787 =
                                               let uu____16794 =
                                                 let uu____16795 =
                                                   let uu____16802 =
                                                     let uu____16803 =
                                                       let uu____16804 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16804
                                                        in
                                                     let uu____16805 =
                                                       let uu____16808 =
                                                         let uu____16809 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16809
                                                          in
                                                       [uu____16808]  in
                                                     uu____16803 ::
                                                       uu____16805
                                                      in
                                                   (bind1, uu____16802)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16795
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16794
                                                in
                                             uu____16787
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16815 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____16827 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____16827
                                         then
                                           let uu____16836 =
                                             let uu____16843 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16843
                                              in
                                           let uu____16844 =
                                             let uu____16853 =
                                               let uu____16860 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____16860
                                                in
                                             [uu____16853]  in
                                           uu____16836 :: uu____16844
                                         else []  in
                                       let reified =
                                         let uu____16889 =
                                           let uu____16896 =
                                             let uu____16897 =
                                               let uu____16912 =
                                                 let uu____16921 =
                                                   let uu____16930 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____16937 =
                                                     let uu____16946 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____16946]  in
                                                   uu____16930 :: uu____16937
                                                    in
                                                 let uu____16971 =
                                                   let uu____16980 =
                                                     let uu____16989 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16996 =
                                                       let uu____17005 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____17012 =
                                                         let uu____17021 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____17028 =
                                                           let uu____17037 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____17037]  in
                                                         uu____17021 ::
                                                           uu____17028
                                                          in
                                                       uu____17005 ::
                                                         uu____17012
                                                        in
                                                     uu____16989 ::
                                                       uu____16996
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____16980
                                                    in
                                                 FStar_List.append
                                                   uu____16921 uu____16971
                                                  in
                                               (bind_inst, uu____16912)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16897
                                              in
                                           FStar_Syntax_Syntax.mk uu____16896
                                            in
                                         uu____16889
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____17103  ->
                                            let uu____17104 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____17105 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____17104 uu____17105);
                                       (let uu____17106 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____17106 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____17130 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____17130
                        in
                     let uu____17131 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____17131 with
                      | (uu____17132,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____17169 =
                                  let uu____17170 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____17170.FStar_Syntax_Syntax.n  in
                                match uu____17169 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____17174) -> t2
                                | uu____17179 -> head4  in
                              let uu____17180 =
                                let uu____17181 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____17181.FStar_Syntax_Syntax.n  in
                              match uu____17180 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____17187 -> FStar_Pervasives_Native.None
                               in
                            let uu____17188 = maybe_extract_fv head4  in
                            match uu____17188 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____17198 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____17198
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____17203 = maybe_extract_fv head5
                                     in
                                  match uu____17203 with
                                  | FStar_Pervasives_Native.Some uu____17208
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____17209 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____17214 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____17229 =
                              match uu____17229 with
                              | (e,q) ->
                                  let uu____17236 =
                                    let uu____17237 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____17237.FStar_Syntax_Syntax.n  in
                                  (match uu____17236 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____17252 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____17252
                                   | uu____17253 -> false)
                               in
                            let uu____17254 =
                              let uu____17255 =
                                let uu____17264 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____17264 :: args  in
                              FStar_Util.for_some is_arg_impure uu____17255
                               in
                            if uu____17254
                            then
                              let uu____17283 =
                                let uu____17284 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____17284
                                 in
                              failwith uu____17283
                            else ());
                           (let uu____17286 = maybe_unfold_action head_app
                               in
                            match uu____17286 with
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
                                   (fun uu____17329  ->
                                      let uu____17330 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____17331 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____17330 uu____17331);
                                 (let uu____17332 = FStar_List.tl stack  in
                                  norm cfg env uu____17332 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____17334) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____17358 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____17358  in
                     (log cfg
                        (fun uu____17362  ->
                           let uu____17363 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____17363);
                      (let uu____17364 = FStar_List.tl stack  in
                       norm cfg env uu____17364 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____17485  ->
                               match uu____17485 with
                               | (pat,wopt,tm) ->
                                   let uu____17533 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____17533)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____17565 = FStar_List.tl stack  in
                     norm cfg env uu____17565 tm
                 | uu____17566 -> fallback ())

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
              (fun uu____17580  ->
                 let uu____17581 = FStar_Ident.string_of_lid msrc  in
                 let uu____17582 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17583 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17581
                   uu____17582 uu____17583);
            (let uu____17584 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____17584
             then
               let ed =
                 let uu____17586 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____17586  in
               let uu____17587 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____17587 with
               | (uu____17588,return_repr) ->
                   let return_inst =
                     let uu____17601 =
                       let uu____17602 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17602.FStar_Syntax_Syntax.n  in
                     match uu____17601 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17608::[]) ->
                         let uu____17613 =
                           let uu____17620 =
                             let uu____17621 =
                               let uu____17628 =
                                 let uu____17629 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17629]  in
                               (return_tm, uu____17628)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17621  in
                           FStar_Syntax_Syntax.mk uu____17620  in
                         uu____17613 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17635 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17638 =
                     let uu____17645 =
                       let uu____17646 =
                         let uu____17661 =
                           let uu____17670 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17677 =
                             let uu____17686 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17686]  in
                           uu____17670 :: uu____17677  in
                         (return_inst, uu____17661)  in
                       FStar_Syntax_Syntax.Tm_app uu____17646  in
                     FStar_Syntax_Syntax.mk uu____17645  in
                   uu____17638 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17725 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17725 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17728 =
                      let uu____17729 = FStar_Ident.text_of_lid msrc  in
                      let uu____17730 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17729 uu____17730
                       in
                    failwith uu____17728
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17731;
                      FStar_TypeChecker_Env.mtarget = uu____17732;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17733;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17755 =
                      let uu____17756 = FStar_Ident.text_of_lid msrc  in
                      let uu____17757 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17756 uu____17757
                       in
                    failwith uu____17755
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17758;
                      FStar_TypeChecker_Env.mtarget = uu____17759;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17760;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____17795 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____17796 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____17795 t FStar_Syntax_Syntax.tun uu____17796))

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
                (fun uu____17852  ->
                   match uu____17852 with
                   | (a,imp) ->
                       let uu____17863 = norm cfg env [] a  in
                       (uu____17863, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____17871  ->
             let uu____17872 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17873 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____17872 uu____17873);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17897 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____17897
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___207_17900 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___207_17900.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___207_17900.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17922 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                     uu____17922
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___208_17925 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___208_17925.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___208_17925.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17962  ->
                      match uu____17962 with
                      | (a,i) ->
                          let uu____17973 = norm cfg env [] a  in
                          (uu____17973, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___120_17991  ->
                       match uu___120_17991 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17995 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17995
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___209_18003 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___210_18006 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___210_18006.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___209_18003.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___209_18003.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____18009  ->
        match uu____18009 with
        | (x,imp) ->
            let uu____18012 =
              let uu___211_18013 = x  in
              let uu____18014 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___211_18013.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___211_18013.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____18014
              }  in
            (uu____18012, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____18020 =
          FStar_List.fold_left
            (fun uu____18054  ->
               fun b  ->
                 match uu____18054 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____18020 with | (nbs,uu____18134) -> FStar_List.rev nbs

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
            let uu____18166 =
              let uu___212_18167 = rc  in
              let uu____18168 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___212_18167.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____18168;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___212_18167.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____18166
        | uu____18177 -> lopt

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
            (let uu____18198 = FStar_Syntax_Print.term_to_string tm  in
             let uu____18199 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____18198
               uu____18199)
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
          let uu____18221 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____18221
          then tm1
          else
            (let w t =
               let uu___213_18235 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___213_18235.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___213_18235.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____18246 =
                 let uu____18247 = FStar_Syntax_Util.unmeta t  in
                 uu____18247.FStar_Syntax_Syntax.n  in
               match uu____18246 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____18254 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____18303)::args1,(bv,uu____18306)::bs1) ->
                   let uu____18340 =
                     let uu____18341 = FStar_Syntax_Subst.compress t  in
                     uu____18341.FStar_Syntax_Syntax.n  in
                   (match uu____18340 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____18345 -> false)
               | ([],[]) -> true
               | (uu____18366,uu____18367) -> false  in
             let is_applied bs t =
               if (cfg.debug).wpe
               then
                 (let uu____18408 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18409 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____18408
                    uu____18409)
               else ();
               (let uu____18411 = FStar_Syntax_Util.head_and_args' t  in
                match uu____18411 with
                | (hd1,args) ->
                    let uu____18444 =
                      let uu____18445 = FStar_Syntax_Subst.compress hd1  in
                      uu____18445.FStar_Syntax_Syntax.n  in
                    (match uu____18444 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if (cfg.debug).wpe
                          then
                            (let uu____18452 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____18453 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____18454 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____18452 uu____18453 uu____18454)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____18456 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.debug).wpe
               then
                 (let uu____18473 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18474 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18473
                    uu____18474)
               else ();
               (let uu____18476 = FStar_Syntax_Util.is_squash t  in
                match uu____18476 with
                | FStar_Pervasives_Native.Some (uu____18487,t') ->
                    is_applied bs t'
                | uu____18499 ->
                    let uu____18508 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____18508 with
                     | FStar_Pervasives_Native.Some (uu____18519,t') ->
                         is_applied bs t'
                     | uu____18531 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____18555 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18555 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18562)::(q,uu____18564)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____18592 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18593 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18592 uu____18593)
                    else ();
                    (let uu____18595 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18595 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18600 =
                           let uu____18601 = FStar_Syntax_Subst.compress p
                              in
                           uu____18601.FStar_Syntax_Syntax.n  in
                         (match uu____18600 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18609 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18609))
                          | uu____18612 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18615)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18632 =
                           let uu____18633 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18633.FStar_Syntax_Syntax.n  in
                         (match uu____18632 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if (cfg.debug).wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18641 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18641))
                          | uu____18644 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18648 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18648 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18653 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18653 with
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
                                     let uu____18664 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18664))
                               | uu____18667 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18672)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18689 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18689 with
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
                                     let uu____18700 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18700))
                               | uu____18703 -> FStar_Pervasives_Native.None)
                          | uu____18706 -> FStar_Pervasives_Native.None)
                     | uu____18709 -> FStar_Pervasives_Native.None))
               | uu____18712 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18725 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18725 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18731)::[],uu____18732,phi')) ->
                   (if (cfg.debug).wpe
                    then
                      (let uu____18743 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18744 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18743
                         uu____18744)
                    else ();
                    is_quantified_const bv phi')
               | uu____18746 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18759 =
                 let uu____18760 = FStar_Syntax_Subst.compress phi  in
                 uu____18760.FStar_Syntax_Syntax.n  in
               match uu____18759 with
               | FStar_Syntax_Syntax.Tm_match (uu____18765,br::brs) ->
                   let uu____18832 = br  in
                   (match uu____18832 with
                    | (uu____18849,uu____18850,e) ->
                        let r =
                          let uu____18871 = simp_t e  in
                          match uu____18871 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18877 =
                                FStar_List.for_all
                                  (fun uu____18895  ->
                                     match uu____18895 with
                                     | (uu____18908,uu____18909,e') ->
                                         let uu____18923 = simp_t e'  in
                                         uu____18923 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18877
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18931 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18940 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18940
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18971 =
                 match uu____18971 with
                 | (t1,q) ->
                     let uu____18984 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18984 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____19012 -> (t1, q))
                  in
               let uu____19023 = FStar_Syntax_Util.head_and_args t  in
               match uu____19023 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____19089 =
                 let uu____19090 = FStar_Syntax_Util.unmeta ty  in
                 uu____19090.FStar_Syntax_Syntax.n  in
               match uu____19089 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____19094) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____19099,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____19119 -> false  in
             let simplify1 arg =
               let uu____19144 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____19144, arg)  in
             let uu____19153 = is_forall_const tm1  in
             match uu____19153 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if (cfg.debug).wpe
                  then
                    (let uu____19158 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____19159 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____19158
                       uu____19159)
                  else ();
                  (let uu____19161 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____19161))
             | FStar_Pervasives_Native.None  ->
                 let uu____19162 =
                   let uu____19163 = FStar_Syntax_Subst.compress tm1  in
                   uu____19163.FStar_Syntax_Syntax.n  in
                 (match uu____19162 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____19167;
                              FStar_Syntax_Syntax.vars = uu____19168;_},uu____19169);
                         FStar_Syntax_Syntax.pos = uu____19170;
                         FStar_Syntax_Syntax.vars = uu____19171;_},args)
                      ->
                      let uu____19197 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19197
                      then
                        let uu____19198 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____19198 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19243)::
                             (uu____19244,(arg,uu____19246))::[] ->
                             maybe_auto_squash arg
                         | (uu____19295,(arg,uu____19297))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19298)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19347)::uu____19348::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19399::(FStar_Pervasives_Native.Some (false
                                         ),uu____19400)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19451 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19465 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19465
                         then
                           let uu____19466 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19466 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19511)::uu____19512::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19563::(FStar_Pervasives_Native.Some (true
                                           ),uu____19564)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19615)::(uu____19616,(arg,uu____19618))::[]
                               -> maybe_auto_squash arg
                           | (uu____19667,(arg,uu____19669))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19670)::[]
                               -> maybe_auto_squash arg
                           | uu____19719 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19733 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19733
                            then
                              let uu____19734 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19734 with
                              | uu____19779::(FStar_Pervasives_Native.Some
                                              (true ),uu____19780)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19831)::uu____19832::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19883)::(uu____19884,(arg,uu____19886))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19935,(p,uu____19937))::(uu____19938,
                                                                (q,uu____19940))::[]
                                  ->
                                  let uu____19987 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19987
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19989 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20003 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20003
                               then
                                 let uu____20004 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____20004 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20049)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20050)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20101)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20102)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20153)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20154)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20205)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20206)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20257,(arg,uu____20259))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20260)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20309)::(uu____20310,(arg,uu____20312))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20361,(arg,uu____20363))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20364)::[]
                                     ->
                                     let uu____20413 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20413
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20414)::(uu____20415,(arg,uu____20417))::[]
                                     ->
                                     let uu____20466 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20466
                                 | (uu____20467,(p,uu____20469))::(uu____20470,
                                                                   (q,uu____20472))::[]
                                     ->
                                     let uu____20519 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20519
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20521 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20535 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20535
                                  then
                                    let uu____20536 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20536 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20581)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20612)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20643 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20657 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20657
                                     then
                                       match args with
                                       | (t,uu____20659)::[] ->
                                           let uu____20676 =
                                             let uu____20677 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20677.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20676 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20680::[],body,uu____20682)
                                                ->
                                                let uu____20709 = simp_t body
                                                   in
                                                (match uu____20709 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20712 -> tm1)
                                            | uu____20715 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20717))::(t,uu____20719)::[]
                                           ->
                                           let uu____20746 =
                                             let uu____20747 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20747.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20746 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20750::[],body,uu____20752)
                                                ->
                                                let uu____20779 = simp_t body
                                                   in
                                                (match uu____20779 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20782 -> tm1)
                                            | uu____20785 -> tm1)
                                       | uu____20786 -> tm1
                                     else
                                       (let uu____20796 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20796
                                        then
                                          match args with
                                          | (t,uu____20798)::[] ->
                                              let uu____20815 =
                                                let uu____20816 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20816.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20815 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20819::[],body,uu____20821)
                                                   ->
                                                   let uu____20848 =
                                                     simp_t body  in
                                                   (match uu____20848 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20851 -> tm1)
                                               | uu____20854 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20856))::(t,uu____20858)::[]
                                              ->
                                              let uu____20885 =
                                                let uu____20886 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20886.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20885 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20889::[],body,uu____20891)
                                                   ->
                                                   let uu____20918 =
                                                     simp_t body  in
                                                   (match uu____20918 with
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
                                                    | uu____20921 -> tm1)
                                               | uu____20924 -> tm1)
                                          | uu____20925 -> tm1
                                        else
                                          (let uu____20935 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20935
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20936;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20937;_},uu____20938)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20955;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20956;_},uu____20957)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20974 -> tm1
                                           else
                                             (let uu____20984 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20984 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____21004 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____21014;
                         FStar_Syntax_Syntax.vars = uu____21015;_},args)
                      ->
                      let uu____21037 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21037
                      then
                        let uu____21038 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____21038 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21083)::
                             (uu____21084,(arg,uu____21086))::[] ->
                             maybe_auto_squash arg
                         | (uu____21135,(arg,uu____21137))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____21138)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____21187)::uu____21188::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____21239::(FStar_Pervasives_Native.Some (false
                                         ),uu____21240)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21291 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21305 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21305
                         then
                           let uu____21306 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21306 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21351)::uu____21352::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21403::(FStar_Pervasives_Native.Some (true
                                           ),uu____21404)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21455)::(uu____21456,(arg,uu____21458))::[]
                               -> maybe_auto_squash arg
                           | (uu____21507,(arg,uu____21509))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21510)::[]
                               -> maybe_auto_squash arg
                           | uu____21559 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21573 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21573
                            then
                              let uu____21574 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21574 with
                              | uu____21619::(FStar_Pervasives_Native.Some
                                              (true ),uu____21620)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21671)::uu____21672::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21723)::(uu____21724,(arg,uu____21726))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21775,(p,uu____21777))::(uu____21778,
                                                                (q,uu____21780))::[]
                                  ->
                                  let uu____21827 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21827
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21829 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21843 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21843
                               then
                                 let uu____21844 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21844 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21889)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21890)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21941)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21942)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21993)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21994)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22045)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22046)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____22097,(arg,uu____22099))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____22100)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22149)::(uu____22150,(arg,uu____22152))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____22201,(arg,uu____22203))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____22204)::[]
                                     ->
                                     let uu____22253 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22253
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22254)::(uu____22255,(arg,uu____22257))::[]
                                     ->
                                     let uu____22306 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22306
                                 | (uu____22307,(p,uu____22309))::(uu____22310,
                                                                   (q,uu____22312))::[]
                                     ->
                                     let uu____22359 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22359
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22361 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22375 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22375
                                  then
                                    let uu____22376 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22376 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22421)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22452)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22483 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22497 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22497
                                     then
                                       match args with
                                       | (t,uu____22499)::[] ->
                                           let uu____22516 =
                                             let uu____22517 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22517.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22516 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22520::[],body,uu____22522)
                                                ->
                                                let uu____22549 = simp_t body
                                                   in
                                                (match uu____22549 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22552 -> tm1)
                                            | uu____22555 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22557))::(t,uu____22559)::[]
                                           ->
                                           let uu____22586 =
                                             let uu____22587 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22587.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22586 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22590::[],body,uu____22592)
                                                ->
                                                let uu____22619 = simp_t body
                                                   in
                                                (match uu____22619 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22622 -> tm1)
                                            | uu____22625 -> tm1)
                                       | uu____22626 -> tm1
                                     else
                                       (let uu____22636 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22636
                                        then
                                          match args with
                                          | (t,uu____22638)::[] ->
                                              let uu____22655 =
                                                let uu____22656 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22656.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22655 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22659::[],body,uu____22661)
                                                   ->
                                                   let uu____22688 =
                                                     simp_t body  in
                                                   (match uu____22688 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22691 -> tm1)
                                               | uu____22694 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22696))::(t,uu____22698)::[]
                                              ->
                                              let uu____22725 =
                                                let uu____22726 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22726.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22725 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22729::[],body,uu____22731)
                                                   ->
                                                   let uu____22758 =
                                                     simp_t body  in
                                                   (match uu____22758 with
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
                                                    | uu____22761 -> tm1)
                                               | uu____22764 -> tm1)
                                          | uu____22765 -> tm1
                                        else
                                          (let uu____22775 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22775
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22776;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22777;_},uu____22778)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22795;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22796;_},uu____22797)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22814 -> tm1
                                           else
                                             (let uu____22824 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22824 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22844 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____22859 = simp_t t  in
                      (match uu____22859 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22862 ->
                      let uu____22885 = is_const_match tm1  in
                      (match uu____22885 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____22888 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____22898  ->
               (let uu____22900 = FStar_Syntax_Print.tag_of_term t  in
                let uu____22901 = FStar_Syntax_Print.term_to_string t  in
                let uu____22902 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____22909 =
                  let uu____22910 =
                    let uu____22913 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____22913
                     in
                  stack_to_string uu____22910  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____22900 uu____22901 uu____22902 uu____22909);
               (let uu____22936 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____22936
                then
                  let uu____22937 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____22937 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____22944 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____22945 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____22946 =
                          let uu____22947 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____22947
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____22944
                          uu____22945 uu____22946);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____22965 =
                     let uu____22966 =
                       let uu____22967 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____22967  in
                     FStar_Util.string_of_int uu____22966  in
                   let uu____22972 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____22973 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____22965 uu____22972 uu____22973)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____22979,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____23030  ->
                     let uu____23031 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____23031);
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
               let uu____23069 =
                 let uu___214_23070 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___214_23070.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___214_23070.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____23069
           | (Arg (Univ uu____23073,uu____23074,uu____23075))::uu____23076 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____23079,uu____23080))::uu____23081 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____23096,uu____23097),aq,r))::stack1
               when
               let uu____23147 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____23147 ->
               let t2 =
                 let uu____23151 =
                   let uu____23156 =
                     let uu____23157 = closure_as_term cfg env_arg tm  in
                     (uu____23157, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____23156  in
                 uu____23151 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____23167),aq,r))::stack1 ->
               (log cfg
                  (fun uu____23220  ->
                     let uu____23221 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____23221);
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
                  (let uu____23233 = FStar_ST.op_Bang m  in
                   match uu____23233 with
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
                   | FStar_Pervasives_Native.Some (uu____23376,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____23429 =
                 log cfg
                   (fun uu____23433  ->
                      let uu____23434 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____23434);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____23440 =
                 let uu____23441 = FStar_Syntax_Subst.compress t1  in
                 uu____23441.FStar_Syntax_Syntax.n  in
               (match uu____23440 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____23468 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____23468  in
                    (log cfg
                       (fun uu____23472  ->
                          let uu____23473 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____23473);
                     (let uu____23474 = FStar_List.tl stack  in
                      norm cfg env1 uu____23474 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____23475);
                       FStar_Syntax_Syntax.pos = uu____23476;
                       FStar_Syntax_Syntax.vars = uu____23477;_},(e,uu____23479)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____23508 when
                    (cfg.steps).primops ->
                    let uu____23523 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____23523 with
                     | (hd1,args) ->
                         let uu____23560 =
                           let uu____23561 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____23561.FStar_Syntax_Syntax.n  in
                         (match uu____23560 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____23565 = find_prim_step cfg fv  in
                              (match uu____23565 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____23568; arity = uu____23569;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____23571;
                                     requires_binder_substitution =
                                       uu____23572;
                                     interpretation = uu____23573;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____23589 -> fallback " (3)" ())
                          | uu____23592 -> fallback " (4)" ()))
                | uu____23593 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____23616  ->
                     let uu____23617 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____23617);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____23626 =
                   log cfg1
                     (fun uu____23631  ->
                        let uu____23632 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____23633 =
                          let uu____23634 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____23661  ->
                                    match uu____23661 with
                                    | (p,uu____23671,uu____23672) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____23634
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____23632 uu____23633);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___121_23689  ->
                                match uu___121_23689 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____23690 -> false))
                         in
                      let steps =
                        let uu___215_23692 = cfg1.steps  in
                        {
                          beta = (uu___215_23692.beta);
                          iota = (uu___215_23692.iota);
                          zeta = false;
                          weak = (uu___215_23692.weak);
                          hnf = (uu___215_23692.hnf);
                          primops = (uu___215_23692.primops);
                          do_not_unfold_pure_lets =
                            (uu___215_23692.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___215_23692.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___215_23692.pure_subterms_within_computations);
                          simplify = (uu___215_23692.simplify);
                          erase_universes = (uu___215_23692.erase_universes);
                          allow_unbound_universes =
                            (uu___215_23692.allow_unbound_universes);
                          reify_ = (uu___215_23692.reify_);
                          compress_uvars = (uu___215_23692.compress_uvars);
                          no_full_norm = (uu___215_23692.no_full_norm);
                          check_no_uvars = (uu___215_23692.check_no_uvars);
                          unmeta = (uu___215_23692.unmeta);
                          unascribe = (uu___215_23692.unascribe);
                          in_full_norm_request =
                            (uu___215_23692.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___215_23692.weakly_reduce_scrutinee)
                        }  in
                      let uu___216_23697 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___216_23697.tcenv);
                        debug = (uu___216_23697.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___216_23697.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___216_23697.memoize_lazy);
                        normalize_pure_lets =
                          (uu___216_23697.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____23769 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____23798 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____23882  ->
                                    fun uu____23883  ->
                                      match (uu____23882, uu____23883) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____24022 = norm_pat env3 p1
                                             in
                                          (match uu____24022 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____23798 with
                           | (pats1,env3) ->
                               ((let uu___217_24184 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___217_24184.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___218_24203 = x  in
                            let uu____24204 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___218_24203.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___218_24203.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____24204
                            }  in
                          ((let uu___219_24218 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___219_24218.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___220_24229 = x  in
                            let uu____24230 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___220_24229.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___220_24229.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____24230
                            }  in
                          ((let uu___221_24244 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___221_24244.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___222_24260 = x  in
                            let uu____24261 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___222_24260.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___222_24260.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____24261
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___223_24276 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___223_24276.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____24320 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____24336 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____24336 with
                                  | (p,wopt,e) ->
                                      let uu____24356 = norm_pat env1 p  in
                                      (match uu____24356 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____24411 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____24411
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____24424 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____24424
                      then
                        norm
                          (let uu___224_24429 = cfg1  in
                           {
                             steps =
                               (let uu___225_24432 = cfg1.steps  in
                                {
                                  beta = (uu___225_24432.beta);
                                  iota = (uu___225_24432.iota);
                                  zeta = (uu___225_24432.zeta);
                                  weak = (uu___225_24432.weak);
                                  hnf = (uu___225_24432.hnf);
                                  primops = (uu___225_24432.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___225_24432.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___225_24432.unfold_until);
                                  unfold_only = (uu___225_24432.unfold_only);
                                  unfold_fully =
                                    (uu___225_24432.unfold_fully);
                                  unfold_attr = (uu___225_24432.unfold_attr);
                                  unfold_tac = (uu___225_24432.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___225_24432.pure_subterms_within_computations);
                                  simplify = (uu___225_24432.simplify);
                                  erase_universes =
                                    (uu___225_24432.erase_universes);
                                  allow_unbound_universes =
                                    (uu___225_24432.allow_unbound_universes);
                                  reify_ = (uu___225_24432.reify_);
                                  compress_uvars =
                                    (uu___225_24432.compress_uvars);
                                  no_full_norm =
                                    (uu___225_24432.no_full_norm);
                                  check_no_uvars =
                                    (uu___225_24432.check_no_uvars);
                                  unmeta = (uu___225_24432.unmeta);
                                  unascribe = (uu___225_24432.unascribe);
                                  in_full_norm_request =
                                    (uu___225_24432.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___224_24429.tcenv);
                             debug = (uu___224_24429.debug);
                             delta_level = (uu___224_24429.delta_level);
                             primitive_steps =
                               (uu___224_24429.primitive_steps);
                             strong = (uu___224_24429.strong);
                             memoize_lazy = (uu___224_24429.memoize_lazy);
                             normalize_pure_lets =
                               (uu___224_24429.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____24434 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____24434)
                    in
                 let rec is_cons head1 =
                   let uu____24459 =
                     let uu____24460 = FStar_Syntax_Subst.compress head1  in
                     uu____24460.FStar_Syntax_Syntax.n  in
                   match uu____24459 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____24464) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____24469 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____24470;
                         FStar_Syntax_Syntax.fv_delta = uu____24471;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____24472;
                         FStar_Syntax_Syntax.fv_delta = uu____24473;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____24474);_}
                       -> true
                   | uu____24481 -> false  in
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
                   let uu____24644 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____24644 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____24731 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____24770 ->
                                 let uu____24771 =
                                   let uu____24772 = is_cons head1  in
                                   Prims.op_Negation uu____24772  in
                                 FStar_Util.Inr uu____24771)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____24797 =
                              let uu____24798 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____24798.FStar_Syntax_Syntax.n  in
                            (match uu____24797 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____24816 ->
                                 let uu____24817 =
                                   let uu____24818 = is_cons head1  in
                                   Prims.op_Negation uu____24818  in
                                 FStar_Util.Inr uu____24817))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____24895)::rest_a,(p1,uu____24898)::rest_p) ->
                       let uu____24942 = matches_pat t2 p1  in
                       (match uu____24942 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____24991 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____25109 = matches_pat scrutinee1 p1  in
                       (match uu____25109 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____25149  ->
                                  let uu____25150 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____25151 =
                                    let uu____25152 =
                                      FStar_List.map
                                        (fun uu____25162  ->
                                           match uu____25162 with
                                           | (uu____25167,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____25152
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____25150 uu____25151);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____25199  ->
                                       match uu____25199 with
                                       | (bv,t2) ->
                                           let uu____25222 =
                                             let uu____25229 =
                                               let uu____25232 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____25232
                                                in
                                             let uu____25233 =
                                               let uu____25234 =
                                                 let uu____25265 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____25265, false)
                                                  in
                                               Clos uu____25234  in
                                             (uu____25229, uu____25233)  in
                                           uu____25222 :: env2) env1 s
                                 in
                              let uu____25378 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____25378)))
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
    let uu____25405 =
      let uu____25408 = FStar_ST.op_Bang plugins  in p :: uu____25408  in
    FStar_ST.op_Colon_Equals plugins uu____25405  in
  let retrieve uu____25516 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : unit -> primitive_step Prims.list) =
  fun uu____25593  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___122_25634  ->
                  match uu___122_25634 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____25638 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____25644 -> d  in
        let uu____25647 = to_fsteps s  in
        let uu____25648 =
          let uu____25649 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____25650 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____25651 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____25652 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "WPE")  in
          let uu____25653 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____25654 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____25649;
            primop = uu____25650;
            b380 = uu____25651;
            wpe = uu____25652;
            norm_delayed = uu____25653;
            print_normalized = uu____25654
          }  in
        let uu____25655 =
          let uu____25658 =
            let uu____25661 = retrieve_plugins ()  in
            FStar_List.append uu____25661 psteps  in
          add_steps built_in_primitive_steps uu____25658  in
        let uu____25664 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____25666 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____25666)
           in
        {
          steps = uu____25647;
          tcenv = e;
          debug = uu____25648;
          delta_level = d1;
          primitive_steps = uu____25655;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____25664
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
      fun t  -> let uu____25748 = config s e  in norm_comp uu____25748 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____25765 = config [] env  in norm_universe uu____25765 [] u
  
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
        let uu____25789 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25789  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____25796 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___226_25815 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___226_25815.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___226_25815.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____25822 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____25822
          then
            let ct1 =
              let uu____25824 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____25824 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____25831 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____25831
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___227_25835 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___227_25835.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___227_25835.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___227_25835.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___228_25837 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___228_25837.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___228_25837.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___228_25837.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___228_25837.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___229_25838 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___229_25838.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___229_25838.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____25840 -> c
  
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
        let uu____25858 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25858  in
      let uu____25865 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____25865
      then
        let uu____25866 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____25866 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____25872  ->
                 let uu____25873 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____25873)
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
            ((let uu____25894 =
                let uu____25899 =
                  let uu____25900 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25900
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____25899)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____25894);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____25915 = config [AllowUnboundUniverses] env  in
          norm_comp uu____25915 [] c
        with
        | e ->
            ((let uu____25928 =
                let uu____25933 =
                  let uu____25934 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25934
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____25933)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____25928);
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
                   let uu____25979 =
                     let uu____25980 =
                       let uu____25987 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____25987)  in
                     FStar_Syntax_Syntax.Tm_refine uu____25980  in
                   mk uu____25979 t01.FStar_Syntax_Syntax.pos
               | uu____25992 -> t2)
          | uu____25993 -> t2  in
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
        let uu____26057 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____26057 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____26086 ->
                 let uu____26093 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____26093 with
                  | (actuals,uu____26103,uu____26104) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____26118 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____26118 with
                         | (binders,args) ->
                             let uu____26129 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____26129
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
      | uu____26143 ->
          let uu____26144 = FStar_Syntax_Util.head_and_args t  in
          (match uu____26144 with
           | (head1,args) ->
               let uu____26181 =
                 let uu____26182 = FStar_Syntax_Subst.compress head1  in
                 uu____26182.FStar_Syntax_Syntax.n  in
               (match uu____26181 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____26207 =
                      let uu____26220 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____26220  in
                    (match uu____26207 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____26250 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___234_26258 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___234_26258.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___234_26258.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___234_26258.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___234_26258.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___234_26258.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___234_26258.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___234_26258.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___234_26258.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___234_26258.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___234_26258.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___234_26258.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___234_26258.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___234_26258.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___234_26258.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___234_26258.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___234_26258.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___234_26258.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___234_26258.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___234_26258.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___234_26258.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___234_26258.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___234_26258.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___234_26258.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___234_26258.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___234_26258.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___234_26258.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___234_26258.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___234_26258.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___234_26258.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___234_26258.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___234_26258.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___234_26258.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___234_26258.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___234_26258.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___234_26258.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___234_26258.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____26250 with
                            | (uu____26259,ty,uu____26261) ->
                                eta_expand_with_type env t ty))
                | uu____26262 ->
                    let uu____26263 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___235_26271 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___235_26271.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___235_26271.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___235_26271.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___235_26271.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___235_26271.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___235_26271.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___235_26271.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___235_26271.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___235_26271.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___235_26271.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___235_26271.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___235_26271.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___235_26271.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___235_26271.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___235_26271.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___235_26271.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___235_26271.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___235_26271.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___235_26271.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___235_26271.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___235_26271.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___235_26271.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___235_26271.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___235_26271.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___235_26271.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___235_26271.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___235_26271.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___235_26271.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___235_26271.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___235_26271.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___235_26271.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___235_26271.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___235_26271.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___235_26271.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___235_26271.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___235_26271.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____26263 with
                     | (uu____26272,ty,uu____26274) ->
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
      let uu___236_26347 = x  in
      let uu____26348 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___236_26347.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___236_26347.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____26348
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____26351 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____26376 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____26377 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____26378 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____26379 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____26386 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____26387 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____26388 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___237_26418 = rc  in
          let uu____26419 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____26428 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___237_26418.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____26419;
            FStar_Syntax_Syntax.residual_flags = uu____26428
          }  in
        let uu____26431 =
          let uu____26432 =
            let uu____26449 = elim_delayed_subst_binders bs  in
            let uu____26456 = elim_delayed_subst_term t2  in
            let uu____26459 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____26449, uu____26456, uu____26459)  in
          FStar_Syntax_Syntax.Tm_abs uu____26432  in
        mk1 uu____26431
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____26490 =
          let uu____26491 =
            let uu____26504 = elim_delayed_subst_binders bs  in
            let uu____26511 = elim_delayed_subst_comp c  in
            (uu____26504, uu____26511)  in
          FStar_Syntax_Syntax.Tm_arrow uu____26491  in
        mk1 uu____26490
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____26528 =
          let uu____26529 =
            let uu____26536 = elim_bv bv  in
            let uu____26537 = elim_delayed_subst_term phi  in
            (uu____26536, uu____26537)  in
          FStar_Syntax_Syntax.Tm_refine uu____26529  in
        mk1 uu____26528
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____26564 =
          let uu____26565 =
            let uu____26580 = elim_delayed_subst_term t2  in
            let uu____26583 = elim_delayed_subst_args args  in
            (uu____26580, uu____26583)  in
          FStar_Syntax_Syntax.Tm_app uu____26565  in
        mk1 uu____26564
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___238_26651 = p  in
              let uu____26652 =
                let uu____26653 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____26653  in
              {
                FStar_Syntax_Syntax.v = uu____26652;
                FStar_Syntax_Syntax.p =
                  (uu___238_26651.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___239_26655 = p  in
              let uu____26656 =
                let uu____26657 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____26657  in
              {
                FStar_Syntax_Syntax.v = uu____26656;
                FStar_Syntax_Syntax.p =
                  (uu___239_26655.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___240_26664 = p  in
              let uu____26665 =
                let uu____26666 =
                  let uu____26673 = elim_bv x  in
                  let uu____26674 = elim_delayed_subst_term t0  in
                  (uu____26673, uu____26674)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____26666  in
              {
                FStar_Syntax_Syntax.v = uu____26665;
                FStar_Syntax_Syntax.p =
                  (uu___240_26664.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___241_26697 = p  in
              let uu____26698 =
                let uu____26699 =
                  let uu____26712 =
                    FStar_List.map
                      (fun uu____26735  ->
                         match uu____26735 with
                         | (x,b) ->
                             let uu____26748 = elim_pat x  in
                             (uu____26748, b)) pats
                     in
                  (fv, uu____26712)  in
                FStar_Syntax_Syntax.Pat_cons uu____26699  in
              {
                FStar_Syntax_Syntax.v = uu____26698;
                FStar_Syntax_Syntax.p =
                  (uu___241_26697.FStar_Syntax_Syntax.p)
              }
          | uu____26761 -> p  in
        let elim_branch uu____26785 =
          match uu____26785 with
          | (pat,wopt,t3) ->
              let uu____26811 = elim_pat pat  in
              let uu____26814 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____26817 = elim_delayed_subst_term t3  in
              (uu____26811, uu____26814, uu____26817)
           in
        let uu____26822 =
          let uu____26823 =
            let uu____26846 = elim_delayed_subst_term t2  in
            let uu____26849 = FStar_List.map elim_branch branches  in
            (uu____26846, uu____26849)  in
          FStar_Syntax_Syntax.Tm_match uu____26823  in
        mk1 uu____26822
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____26980 =
          match uu____26980 with
          | (tc,topt) ->
              let uu____27015 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____27025 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____27025
                | FStar_Util.Inr c ->
                    let uu____27027 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____27027
                 in
              let uu____27028 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____27015, uu____27028)
           in
        let uu____27037 =
          let uu____27038 =
            let uu____27065 = elim_delayed_subst_term t2  in
            let uu____27068 = elim_ascription a  in
            (uu____27065, uu____27068, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____27038  in
        mk1 uu____27037
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___242_27129 = lb  in
          let uu____27130 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____27133 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___242_27129.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___242_27129.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____27130;
            FStar_Syntax_Syntax.lbeff =
              (uu___242_27129.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____27133;
            FStar_Syntax_Syntax.lbattrs =
              (uu___242_27129.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___242_27129.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____27136 =
          let uu____27137 =
            let uu____27150 =
              let uu____27157 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____27157)  in
            let uu____27166 = elim_delayed_subst_term t2  in
            (uu____27150, uu____27166)  in
          FStar_Syntax_Syntax.Tm_let uu____27137  in
        mk1 uu____27136
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____27216 =
          let uu____27217 =
            let uu____27224 = elim_delayed_subst_term tm  in
            (uu____27224, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____27217  in
        mk1 uu____27216
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____27235 =
          let uu____27236 =
            let uu____27243 = elim_delayed_subst_term t2  in
            let uu____27246 = elim_delayed_subst_meta md  in
            (uu____27243, uu____27246)  in
          FStar_Syntax_Syntax.Tm_meta uu____27236  in
        mk1 uu____27235

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___123_27255  ->
         match uu___123_27255 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____27259 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____27259
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
        let uu____27282 =
          let uu____27283 =
            let uu____27292 = elim_delayed_subst_term t  in
            (uu____27292, uopt)  in
          FStar_Syntax_Syntax.Total uu____27283  in
        mk1 uu____27282
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____27309 =
          let uu____27310 =
            let uu____27319 = elim_delayed_subst_term t  in
            (uu____27319, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____27310  in
        mk1 uu____27309
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___243_27328 = ct  in
          let uu____27329 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____27332 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____27341 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___243_27328.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___243_27328.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____27329;
            FStar_Syntax_Syntax.effect_args = uu____27332;
            FStar_Syntax_Syntax.flags = uu____27341
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___124_27344  ->
    match uu___124_27344 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____27356 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____27356
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____27389 =
          let uu____27396 = elim_delayed_subst_term t  in (m, uu____27396)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____27389
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____27408 =
          let uu____27417 = elim_delayed_subst_term t  in
          (m1, m2, uu____27417)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____27408
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____27444  ->
         match uu____27444 with
         | (t,q) ->
             let uu____27455 = elim_delayed_subst_term t  in (uu____27455, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____27475  ->
         match uu____27475 with
         | (x,q) ->
             let uu____27486 =
               let uu___244_27487 = x  in
               let uu____27488 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___244_27487.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___244_27487.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____27488
               }  in
             (uu____27486, q)) bs

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
            | (uu____27580,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____27606,FStar_Util.Inl t) ->
                let uu____27624 =
                  let uu____27631 =
                    let uu____27632 =
                      let uu____27645 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____27645)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____27632  in
                  FStar_Syntax_Syntax.mk uu____27631  in
                uu____27624 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____27659 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____27659 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____27689 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____27752 ->
                    let uu____27753 =
                      let uu____27762 =
                        let uu____27763 = FStar_Syntax_Subst.compress t4  in
                        uu____27763.FStar_Syntax_Syntax.n  in
                      (uu____27762, tc)  in
                    (match uu____27753 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____27790) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____27831) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____27870,FStar_Util.Inl uu____27871) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____27894 -> failwith "Impossible")
                 in
              (match uu____27689 with
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
          let uu____28019 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____28019 with
          | (univ_names1,binders1,tc) ->
              let uu____28085 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____28085)
  
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
          let uu____28134 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____28134 with
          | (univ_names1,binders1,tc) ->
              let uu____28200 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____28200)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____28239 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____28239 with
           | (univ_names1,binders1,typ1) ->
               let uu___245_28273 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___245_28273.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___245_28273.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___245_28273.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___245_28273.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___246_28288 = s  in
          let uu____28289 =
            let uu____28290 =
              let uu____28299 = FStar_List.map (elim_uvars env) sigs  in
              (uu____28299, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____28290  in
          {
            FStar_Syntax_Syntax.sigel = uu____28289;
            FStar_Syntax_Syntax.sigrng =
              (uu___246_28288.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___246_28288.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___246_28288.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___246_28288.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____28316 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____28316 with
           | (univ_names1,uu____28336,typ1) ->
               let uu___247_28354 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___247_28354.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___247_28354.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___247_28354.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___247_28354.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____28360 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____28360 with
           | (univ_names1,uu____28380,typ1) ->
               let uu___248_28398 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___248_28398.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___248_28398.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___248_28398.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___248_28398.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____28426 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____28426 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____28451 =
                            let uu____28452 =
                              let uu____28453 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____28453  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____28452
                             in
                          elim_delayed_subst_term uu____28451  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___249_28456 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___249_28456.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___249_28456.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___249_28456.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___249_28456.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___250_28457 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___250_28457.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___250_28457.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___250_28457.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___250_28457.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___251_28463 = s  in
          let uu____28464 =
            let uu____28465 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____28465  in
          {
            FStar_Syntax_Syntax.sigel = uu____28464;
            FStar_Syntax_Syntax.sigrng =
              (uu___251_28463.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___251_28463.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___251_28463.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___251_28463.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____28469 = elim_uvars_aux_t env us [] t  in
          (match uu____28469 with
           | (us1,uu____28489,t1) ->
               let uu___252_28507 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___252_28507.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___252_28507.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___252_28507.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___252_28507.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28508 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____28510 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____28510 with
           | (univs1,binders,signature) ->
               let uu____28544 =
                 let uu____28553 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____28553 with
                 | (univs_opening,univs2) ->
                     let uu____28580 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____28580)
                  in
               (match uu____28544 with
                | (univs_opening,univs_closing) ->
                    let uu____28597 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____28603 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____28604 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____28603, uu____28604)  in
                    (match uu____28597 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____28628 =
                           match uu____28628 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____28646 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____28646 with
                                | (us1,t1) ->
                                    let uu____28657 =
                                      let uu____28666 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____28675 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____28666, uu____28675)  in
                                    (match uu____28657 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____28702 =
                                           let uu____28711 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____28720 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____28711, uu____28720)  in
                                         (match uu____28702 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____28748 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____28748
                                                 in
                                              let uu____28749 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____28749 with
                                               | (uu____28772,uu____28773,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____28792 =
                                                       let uu____28793 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____28793
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____28792
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____28802 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____28802 with
                           | (uu____28819,uu____28820,t1) -> t1  in
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
                             | uu____28894 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____28919 =
                               let uu____28920 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____28920.FStar_Syntax_Syntax.n  in
                             match uu____28919 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____28979 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____29010 =
                               let uu____29011 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____29011.FStar_Syntax_Syntax.n  in
                             match uu____29010 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____29032) ->
                                 let uu____29053 = destruct_action_body body
                                    in
                                 (match uu____29053 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____29098 ->
                                 let uu____29099 = destruct_action_body t  in
                                 (match uu____29099 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____29148 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____29148 with
                           | (action_univs,t) ->
                               let uu____29157 = destruct_action_typ_templ t
                                  in
                               (match uu____29157 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___253_29198 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___253_29198.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___253_29198.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___254_29200 = ed  in
                           let uu____29201 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____29202 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____29203 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____29204 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____29205 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____29206 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____29207 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____29208 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____29209 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____29210 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____29211 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____29212 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____29213 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____29214 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___254_29200.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___254_29200.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____29201;
                             FStar_Syntax_Syntax.bind_wp = uu____29202;
                             FStar_Syntax_Syntax.if_then_else = uu____29203;
                             FStar_Syntax_Syntax.ite_wp = uu____29204;
                             FStar_Syntax_Syntax.stronger = uu____29205;
                             FStar_Syntax_Syntax.close_wp = uu____29206;
                             FStar_Syntax_Syntax.assert_p = uu____29207;
                             FStar_Syntax_Syntax.assume_p = uu____29208;
                             FStar_Syntax_Syntax.null_wp = uu____29209;
                             FStar_Syntax_Syntax.trivial = uu____29210;
                             FStar_Syntax_Syntax.repr = uu____29211;
                             FStar_Syntax_Syntax.return_repr = uu____29212;
                             FStar_Syntax_Syntax.bind_repr = uu____29213;
                             FStar_Syntax_Syntax.actions = uu____29214;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___254_29200.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___255_29217 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___255_29217.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___255_29217.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___255_29217.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___255_29217.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___125_29238 =
            match uu___125_29238 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____29269 = elim_uvars_aux_t env us [] t  in
                (match uu____29269 with
                 | (us1,uu____29297,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___256_29324 = sub_eff  in
            let uu____29325 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____29328 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___256_29324.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___256_29324.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____29325;
              FStar_Syntax_Syntax.lift = uu____29328
            }  in
          let uu___257_29331 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___257_29331.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___257_29331.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___257_29331.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___257_29331.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____29341 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____29341 with
           | (univ_names1,binders1,comp1) ->
               let uu___258_29375 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___258_29375.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___258_29375.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___258_29375.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___258_29375.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____29378 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____29379 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  