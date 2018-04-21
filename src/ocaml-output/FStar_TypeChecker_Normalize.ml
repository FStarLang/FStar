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
let uu___is_Beta : step -> Prims.bool =
  fun projectee  -> match projectee with | Beta  -> true | uu____35 -> false 
let uu___is_Iota : step -> Prims.bool =
  fun projectee  -> match projectee with | Iota  -> true | uu____41 -> false 
let uu___is_Zeta : step -> Prims.bool =
  fun projectee  -> match projectee with | Zeta  -> true | uu____47 -> false 
let uu___is_Exclude : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____54 -> false
  
let __proj__Exclude__item___0 : step -> step =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let uu___is_Weak : step -> Prims.bool =
  fun projectee  -> match projectee with | Weak  -> true | uu____67 -> false 
let uu___is_HNF : step -> Prims.bool =
  fun projectee  -> match projectee with | HNF  -> true | uu____73 -> false 
let uu___is_Primops : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____79 -> false
  
let uu___is_Eager_unfolding : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____85 -> false
  
let uu___is_Inlining : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____91 -> false
  
let uu___is_DoNotUnfoldPureLets : step -> Prims.bool =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____97 -> false
  
let uu___is_UnfoldUntil : step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____104 -> false
  
let __proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth =
  fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let uu___is_UnfoldOnly : step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____120 -> false
  
let __proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let uu___is_UnfoldFully : step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____142 -> false
  
let __proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let uu___is_UnfoldAttr : step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____162 -> false
  
let __proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let uu___is_UnfoldTac : step -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____175 -> false
  
let uu___is_PureSubtermsWithinComputations : step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____181 -> false
  
let uu___is_Simplify : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____187 -> false
  
let uu___is_EraseUniverses : step -> Prims.bool =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____193 -> false
  
let uu___is_AllowUnboundUniverses : step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____199 -> false
  
let uu___is_Reify : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____205 -> false
  
let uu___is_CompressUvars : step -> Prims.bool =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____211 -> false
  
let uu___is_NoFullNorm : step -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____217 -> false
  
let uu___is_CheckNoUvars : step -> Prims.bool =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____223 -> false
  
let uu___is_Unmeta : step -> Prims.bool =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____229 -> false
  
let uu___is_Unascribe : step -> Prims.bool =
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
      fun uu___77_269  ->
        match uu___77_269 with
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
let __proj__Mkfsteps__item__beta : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__iota : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__zeta : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__weak : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__hnf : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__primops : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__do_not_unfold_pure_lets : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__unfold_until :
  fsteps -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option =
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
  
let __proj__Mkfsteps__item__unfold_only :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option =
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
  
let __proj__Mkfsteps__item__unfold_fully :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option =
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
  
let __proj__Mkfsteps__item__unfold_attr :
  fsteps ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option
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
  
let __proj__Mkfsteps__item__unfold_tac : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__pure_subterms_within_computations :
  fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__simplify : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__erase_universes : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__allow_unbound_universes : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__reify_ : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__compress_uvars : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__no_full_norm : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__check_no_uvars : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__unmeta : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__unascribe : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__in_full_norm_request : fsteps -> Prims.bool =
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
  
let __proj__Mkfsteps__item__weakly_reduce_scrutinee : fsteps -> Prims.bool =
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
  
let default_steps : fsteps =
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
let fstep_add_one : step -> fsteps -> fsteps =
  fun s  ->
    fun fs  ->
      let add_opt x uu___78_1503 =
        match uu___78_1503 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___96_1523 = fs  in
          {
            beta = true;
            iota = (uu___96_1523.iota);
            zeta = (uu___96_1523.zeta);
            weak = (uu___96_1523.weak);
            hnf = (uu___96_1523.hnf);
            primops = (uu___96_1523.primops);
            do_not_unfold_pure_lets = (uu___96_1523.do_not_unfold_pure_lets);
            unfold_until = (uu___96_1523.unfold_until);
            unfold_only = (uu___96_1523.unfold_only);
            unfold_fully = (uu___96_1523.unfold_fully);
            unfold_attr = (uu___96_1523.unfold_attr);
            unfold_tac = (uu___96_1523.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1523.pure_subterms_within_computations);
            simplify = (uu___96_1523.simplify);
            erase_universes = (uu___96_1523.erase_universes);
            allow_unbound_universes = (uu___96_1523.allow_unbound_universes);
            reify_ = (uu___96_1523.reify_);
            compress_uvars = (uu___96_1523.compress_uvars);
            no_full_norm = (uu___96_1523.no_full_norm);
            check_no_uvars = (uu___96_1523.check_no_uvars);
            unmeta = (uu___96_1523.unmeta);
            unascribe = (uu___96_1523.unascribe);
            in_full_norm_request = (uu___96_1523.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___96_1523.weakly_reduce_scrutinee)
          }
      | Iota  ->
          let uu___97_1524 = fs  in
          {
            beta = (uu___97_1524.beta);
            iota = true;
            zeta = (uu___97_1524.zeta);
            weak = (uu___97_1524.weak);
            hnf = (uu___97_1524.hnf);
            primops = (uu___97_1524.primops);
            do_not_unfold_pure_lets = (uu___97_1524.do_not_unfold_pure_lets);
            unfold_until = (uu___97_1524.unfold_until);
            unfold_only = (uu___97_1524.unfold_only);
            unfold_fully = (uu___97_1524.unfold_fully);
            unfold_attr = (uu___97_1524.unfold_attr);
            unfold_tac = (uu___97_1524.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1524.pure_subterms_within_computations);
            simplify = (uu___97_1524.simplify);
            erase_universes = (uu___97_1524.erase_universes);
            allow_unbound_universes = (uu___97_1524.allow_unbound_universes);
            reify_ = (uu___97_1524.reify_);
            compress_uvars = (uu___97_1524.compress_uvars);
            no_full_norm = (uu___97_1524.no_full_norm);
            check_no_uvars = (uu___97_1524.check_no_uvars);
            unmeta = (uu___97_1524.unmeta);
            unascribe = (uu___97_1524.unascribe);
            in_full_norm_request = (uu___97_1524.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___97_1524.weakly_reduce_scrutinee)
          }
      | Zeta  ->
          let uu___98_1525 = fs  in
          {
            beta = (uu___98_1525.beta);
            iota = (uu___98_1525.iota);
            zeta = true;
            weak = (uu___98_1525.weak);
            hnf = (uu___98_1525.hnf);
            primops = (uu___98_1525.primops);
            do_not_unfold_pure_lets = (uu___98_1525.do_not_unfold_pure_lets);
            unfold_until = (uu___98_1525.unfold_until);
            unfold_only = (uu___98_1525.unfold_only);
            unfold_fully = (uu___98_1525.unfold_fully);
            unfold_attr = (uu___98_1525.unfold_attr);
            unfold_tac = (uu___98_1525.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1525.pure_subterms_within_computations);
            simplify = (uu___98_1525.simplify);
            erase_universes = (uu___98_1525.erase_universes);
            allow_unbound_universes = (uu___98_1525.allow_unbound_universes);
            reify_ = (uu___98_1525.reify_);
            compress_uvars = (uu___98_1525.compress_uvars);
            no_full_norm = (uu___98_1525.no_full_norm);
            check_no_uvars = (uu___98_1525.check_no_uvars);
            unmeta = (uu___98_1525.unmeta);
            unascribe = (uu___98_1525.unascribe);
            in_full_norm_request = (uu___98_1525.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___98_1525.weakly_reduce_scrutinee)
          }
      | Exclude (Beta ) ->
          let uu___99_1526 = fs  in
          {
            beta = false;
            iota = (uu___99_1526.iota);
            zeta = (uu___99_1526.zeta);
            weak = (uu___99_1526.weak);
            hnf = (uu___99_1526.hnf);
            primops = (uu___99_1526.primops);
            do_not_unfold_pure_lets = (uu___99_1526.do_not_unfold_pure_lets);
            unfold_until = (uu___99_1526.unfold_until);
            unfold_only = (uu___99_1526.unfold_only);
            unfold_fully = (uu___99_1526.unfold_fully);
            unfold_attr = (uu___99_1526.unfold_attr);
            unfold_tac = (uu___99_1526.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1526.pure_subterms_within_computations);
            simplify = (uu___99_1526.simplify);
            erase_universes = (uu___99_1526.erase_universes);
            allow_unbound_universes = (uu___99_1526.allow_unbound_universes);
            reify_ = (uu___99_1526.reify_);
            compress_uvars = (uu___99_1526.compress_uvars);
            no_full_norm = (uu___99_1526.no_full_norm);
            check_no_uvars = (uu___99_1526.check_no_uvars);
            unmeta = (uu___99_1526.unmeta);
            unascribe = (uu___99_1526.unascribe);
            in_full_norm_request = (uu___99_1526.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___99_1526.weakly_reduce_scrutinee)
          }
      | Exclude (Iota ) ->
          let uu___100_1527 = fs  in
          {
            beta = (uu___100_1527.beta);
            iota = false;
            zeta = (uu___100_1527.zeta);
            weak = (uu___100_1527.weak);
            hnf = (uu___100_1527.hnf);
            primops = (uu___100_1527.primops);
            do_not_unfold_pure_lets = (uu___100_1527.do_not_unfold_pure_lets);
            unfold_until = (uu___100_1527.unfold_until);
            unfold_only = (uu___100_1527.unfold_only);
            unfold_fully = (uu___100_1527.unfold_fully);
            unfold_attr = (uu___100_1527.unfold_attr);
            unfold_tac = (uu___100_1527.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1527.pure_subterms_within_computations);
            simplify = (uu___100_1527.simplify);
            erase_universes = (uu___100_1527.erase_universes);
            allow_unbound_universes = (uu___100_1527.allow_unbound_universes);
            reify_ = (uu___100_1527.reify_);
            compress_uvars = (uu___100_1527.compress_uvars);
            no_full_norm = (uu___100_1527.no_full_norm);
            check_no_uvars = (uu___100_1527.check_no_uvars);
            unmeta = (uu___100_1527.unmeta);
            unascribe = (uu___100_1527.unascribe);
            in_full_norm_request = (uu___100_1527.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___100_1527.weakly_reduce_scrutinee)
          }
      | Exclude (Zeta ) ->
          let uu___101_1528 = fs  in
          {
            beta = (uu___101_1528.beta);
            iota = (uu___101_1528.iota);
            zeta = false;
            weak = (uu___101_1528.weak);
            hnf = (uu___101_1528.hnf);
            primops = (uu___101_1528.primops);
            do_not_unfold_pure_lets = (uu___101_1528.do_not_unfold_pure_lets);
            unfold_until = (uu___101_1528.unfold_until);
            unfold_only = (uu___101_1528.unfold_only);
            unfold_fully = (uu___101_1528.unfold_fully);
            unfold_attr = (uu___101_1528.unfold_attr);
            unfold_tac = (uu___101_1528.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1528.pure_subterms_within_computations);
            simplify = (uu___101_1528.simplify);
            erase_universes = (uu___101_1528.erase_universes);
            allow_unbound_universes = (uu___101_1528.allow_unbound_universes);
            reify_ = (uu___101_1528.reify_);
            compress_uvars = (uu___101_1528.compress_uvars);
            no_full_norm = (uu___101_1528.no_full_norm);
            check_no_uvars = (uu___101_1528.check_no_uvars);
            unmeta = (uu___101_1528.unmeta);
            unascribe = (uu___101_1528.unascribe);
            in_full_norm_request = (uu___101_1528.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___101_1528.weakly_reduce_scrutinee)
          }
      | Exclude uu____1529 -> failwith "Bad exclude"
      | Weak  ->
          let uu___102_1530 = fs  in
          {
            beta = (uu___102_1530.beta);
            iota = (uu___102_1530.iota);
            zeta = (uu___102_1530.zeta);
            weak = true;
            hnf = (uu___102_1530.hnf);
            primops = (uu___102_1530.primops);
            do_not_unfold_pure_lets = (uu___102_1530.do_not_unfold_pure_lets);
            unfold_until = (uu___102_1530.unfold_until);
            unfold_only = (uu___102_1530.unfold_only);
            unfold_fully = (uu___102_1530.unfold_fully);
            unfold_attr = (uu___102_1530.unfold_attr);
            unfold_tac = (uu___102_1530.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1530.pure_subterms_within_computations);
            simplify = (uu___102_1530.simplify);
            erase_universes = (uu___102_1530.erase_universes);
            allow_unbound_universes = (uu___102_1530.allow_unbound_universes);
            reify_ = (uu___102_1530.reify_);
            compress_uvars = (uu___102_1530.compress_uvars);
            no_full_norm = (uu___102_1530.no_full_norm);
            check_no_uvars = (uu___102_1530.check_no_uvars);
            unmeta = (uu___102_1530.unmeta);
            unascribe = (uu___102_1530.unascribe);
            in_full_norm_request = (uu___102_1530.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___102_1530.weakly_reduce_scrutinee)
          }
      | HNF  ->
          let uu___103_1531 = fs  in
          {
            beta = (uu___103_1531.beta);
            iota = (uu___103_1531.iota);
            zeta = (uu___103_1531.zeta);
            weak = (uu___103_1531.weak);
            hnf = true;
            primops = (uu___103_1531.primops);
            do_not_unfold_pure_lets = (uu___103_1531.do_not_unfold_pure_lets);
            unfold_until = (uu___103_1531.unfold_until);
            unfold_only = (uu___103_1531.unfold_only);
            unfold_fully = (uu___103_1531.unfold_fully);
            unfold_attr = (uu___103_1531.unfold_attr);
            unfold_tac = (uu___103_1531.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1531.pure_subterms_within_computations);
            simplify = (uu___103_1531.simplify);
            erase_universes = (uu___103_1531.erase_universes);
            allow_unbound_universes = (uu___103_1531.allow_unbound_universes);
            reify_ = (uu___103_1531.reify_);
            compress_uvars = (uu___103_1531.compress_uvars);
            no_full_norm = (uu___103_1531.no_full_norm);
            check_no_uvars = (uu___103_1531.check_no_uvars);
            unmeta = (uu___103_1531.unmeta);
            unascribe = (uu___103_1531.unascribe);
            in_full_norm_request = (uu___103_1531.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___103_1531.weakly_reduce_scrutinee)
          }
      | Primops  ->
          let uu___104_1532 = fs  in
          {
            beta = (uu___104_1532.beta);
            iota = (uu___104_1532.iota);
            zeta = (uu___104_1532.zeta);
            weak = (uu___104_1532.weak);
            hnf = (uu___104_1532.hnf);
            primops = true;
            do_not_unfold_pure_lets = (uu___104_1532.do_not_unfold_pure_lets);
            unfold_until = (uu___104_1532.unfold_until);
            unfold_only = (uu___104_1532.unfold_only);
            unfold_fully = (uu___104_1532.unfold_fully);
            unfold_attr = (uu___104_1532.unfold_attr);
            unfold_tac = (uu___104_1532.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1532.pure_subterms_within_computations);
            simplify = (uu___104_1532.simplify);
            erase_universes = (uu___104_1532.erase_universes);
            allow_unbound_universes = (uu___104_1532.allow_unbound_universes);
            reify_ = (uu___104_1532.reify_);
            compress_uvars = (uu___104_1532.compress_uvars);
            no_full_norm = (uu___104_1532.no_full_norm);
            check_no_uvars = (uu___104_1532.check_no_uvars);
            unmeta = (uu___104_1532.unmeta);
            unascribe = (uu___104_1532.unascribe);
            in_full_norm_request = (uu___104_1532.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___104_1532.weakly_reduce_scrutinee)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | DoNotUnfoldPureLets  ->
          let uu___105_1533 = fs  in
          {
            beta = (uu___105_1533.beta);
            iota = (uu___105_1533.iota);
            zeta = (uu___105_1533.zeta);
            weak = (uu___105_1533.weak);
            hnf = (uu___105_1533.hnf);
            primops = (uu___105_1533.primops);
            do_not_unfold_pure_lets = true;
            unfold_until = (uu___105_1533.unfold_until);
            unfold_only = (uu___105_1533.unfold_only);
            unfold_fully = (uu___105_1533.unfold_fully);
            unfold_attr = (uu___105_1533.unfold_attr);
            unfold_tac = (uu___105_1533.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1533.pure_subterms_within_computations);
            simplify = (uu___105_1533.simplify);
            erase_universes = (uu___105_1533.erase_universes);
            allow_unbound_universes = (uu___105_1533.allow_unbound_universes);
            reify_ = (uu___105_1533.reify_);
            compress_uvars = (uu___105_1533.compress_uvars);
            no_full_norm = (uu___105_1533.no_full_norm);
            check_no_uvars = (uu___105_1533.check_no_uvars);
            unmeta = (uu___105_1533.unmeta);
            unascribe = (uu___105_1533.unascribe);
            in_full_norm_request = (uu___105_1533.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___105_1533.weakly_reduce_scrutinee)
          }
      | UnfoldUntil d ->
          let uu___106_1535 = fs  in
          {
            beta = (uu___106_1535.beta);
            iota = (uu___106_1535.iota);
            zeta = (uu___106_1535.zeta);
            weak = (uu___106_1535.weak);
            hnf = (uu___106_1535.hnf);
            primops = (uu___106_1535.primops);
            do_not_unfold_pure_lets = (uu___106_1535.do_not_unfold_pure_lets);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___106_1535.unfold_only);
            unfold_fully = (uu___106_1535.unfold_fully);
            unfold_attr = (uu___106_1535.unfold_attr);
            unfold_tac = (uu___106_1535.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1535.pure_subterms_within_computations);
            simplify = (uu___106_1535.simplify);
            erase_universes = (uu___106_1535.erase_universes);
            allow_unbound_universes = (uu___106_1535.allow_unbound_universes);
            reify_ = (uu___106_1535.reify_);
            compress_uvars = (uu___106_1535.compress_uvars);
            no_full_norm = (uu___106_1535.no_full_norm);
            check_no_uvars = (uu___106_1535.check_no_uvars);
            unmeta = (uu___106_1535.unmeta);
            unascribe = (uu___106_1535.unascribe);
            in_full_norm_request = (uu___106_1535.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___106_1535.weakly_reduce_scrutinee)
          }
      | UnfoldOnly lids ->
          let uu___107_1539 = fs  in
          {
            beta = (uu___107_1539.beta);
            iota = (uu___107_1539.iota);
            zeta = (uu___107_1539.zeta);
            weak = (uu___107_1539.weak);
            hnf = (uu___107_1539.hnf);
            primops = (uu___107_1539.primops);
            do_not_unfold_pure_lets = (uu___107_1539.do_not_unfold_pure_lets);
            unfold_until = (uu___107_1539.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___107_1539.unfold_fully);
            unfold_attr = (uu___107_1539.unfold_attr);
            unfold_tac = (uu___107_1539.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1539.pure_subterms_within_computations);
            simplify = (uu___107_1539.simplify);
            erase_universes = (uu___107_1539.erase_universes);
            allow_unbound_universes = (uu___107_1539.allow_unbound_universes);
            reify_ = (uu___107_1539.reify_);
            compress_uvars = (uu___107_1539.compress_uvars);
            no_full_norm = (uu___107_1539.no_full_norm);
            check_no_uvars = (uu___107_1539.check_no_uvars);
            unmeta = (uu___107_1539.unmeta);
            unascribe = (uu___107_1539.unascribe);
            in_full_norm_request = (uu___107_1539.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___107_1539.weakly_reduce_scrutinee)
          }
      | UnfoldFully lids ->
          let uu___108_1545 = fs  in
          {
            beta = (uu___108_1545.beta);
            iota = (uu___108_1545.iota);
            zeta = (uu___108_1545.zeta);
            weak = (uu___108_1545.weak);
            hnf = (uu___108_1545.hnf);
            primops = (uu___108_1545.primops);
            do_not_unfold_pure_lets = (uu___108_1545.do_not_unfold_pure_lets);
            unfold_until = (uu___108_1545.unfold_until);
            unfold_only = (uu___108_1545.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___108_1545.unfold_attr);
            unfold_tac = (uu___108_1545.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1545.pure_subterms_within_computations);
            simplify = (uu___108_1545.simplify);
            erase_universes = (uu___108_1545.erase_universes);
            allow_unbound_universes = (uu___108_1545.allow_unbound_universes);
            reify_ = (uu___108_1545.reify_);
            compress_uvars = (uu___108_1545.compress_uvars);
            no_full_norm = (uu___108_1545.no_full_norm);
            check_no_uvars = (uu___108_1545.check_no_uvars);
            unmeta = (uu___108_1545.unmeta);
            unascribe = (uu___108_1545.unascribe);
            in_full_norm_request = (uu___108_1545.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___108_1545.weakly_reduce_scrutinee)
          }
      | UnfoldAttr attr ->
          let uu___109_1549 = fs  in
          {
            beta = (uu___109_1549.beta);
            iota = (uu___109_1549.iota);
            zeta = (uu___109_1549.zeta);
            weak = (uu___109_1549.weak);
            hnf = (uu___109_1549.hnf);
            primops = (uu___109_1549.primops);
            do_not_unfold_pure_lets = (uu___109_1549.do_not_unfold_pure_lets);
            unfold_until = (uu___109_1549.unfold_until);
            unfold_only = (uu___109_1549.unfold_only);
            unfold_fully = (uu___109_1549.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___109_1549.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1549.pure_subterms_within_computations);
            simplify = (uu___109_1549.simplify);
            erase_universes = (uu___109_1549.erase_universes);
            allow_unbound_universes = (uu___109_1549.allow_unbound_universes);
            reify_ = (uu___109_1549.reify_);
            compress_uvars = (uu___109_1549.compress_uvars);
            no_full_norm = (uu___109_1549.no_full_norm);
            check_no_uvars = (uu___109_1549.check_no_uvars);
            unmeta = (uu___109_1549.unmeta);
            unascribe = (uu___109_1549.unascribe);
            in_full_norm_request = (uu___109_1549.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___109_1549.weakly_reduce_scrutinee)
          }
      | UnfoldTac  ->
          let uu___110_1550 = fs  in
          {
            beta = (uu___110_1550.beta);
            iota = (uu___110_1550.iota);
            zeta = (uu___110_1550.zeta);
            weak = (uu___110_1550.weak);
            hnf = (uu___110_1550.hnf);
            primops = (uu___110_1550.primops);
            do_not_unfold_pure_lets = (uu___110_1550.do_not_unfold_pure_lets);
            unfold_until = (uu___110_1550.unfold_until);
            unfold_only = (uu___110_1550.unfold_only);
            unfold_fully = (uu___110_1550.unfold_fully);
            unfold_attr = (uu___110_1550.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___110_1550.pure_subterms_within_computations);
            simplify = (uu___110_1550.simplify);
            erase_universes = (uu___110_1550.erase_universes);
            allow_unbound_universes = (uu___110_1550.allow_unbound_universes);
            reify_ = (uu___110_1550.reify_);
            compress_uvars = (uu___110_1550.compress_uvars);
            no_full_norm = (uu___110_1550.no_full_norm);
            check_no_uvars = (uu___110_1550.check_no_uvars);
            unmeta = (uu___110_1550.unmeta);
            unascribe = (uu___110_1550.unascribe);
            in_full_norm_request = (uu___110_1550.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___110_1550.weakly_reduce_scrutinee)
          }
      | PureSubtermsWithinComputations  ->
          let uu___111_1551 = fs  in
          {
            beta = (uu___111_1551.beta);
            iota = (uu___111_1551.iota);
            zeta = (uu___111_1551.zeta);
            weak = (uu___111_1551.weak);
            hnf = (uu___111_1551.hnf);
            primops = (uu___111_1551.primops);
            do_not_unfold_pure_lets = (uu___111_1551.do_not_unfold_pure_lets);
            unfold_until = (uu___111_1551.unfold_until);
            unfold_only = (uu___111_1551.unfold_only);
            unfold_fully = (uu___111_1551.unfold_fully);
            unfold_attr = (uu___111_1551.unfold_attr);
            unfold_tac = (uu___111_1551.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___111_1551.simplify);
            erase_universes = (uu___111_1551.erase_universes);
            allow_unbound_universes = (uu___111_1551.allow_unbound_universes);
            reify_ = (uu___111_1551.reify_);
            compress_uvars = (uu___111_1551.compress_uvars);
            no_full_norm = (uu___111_1551.no_full_norm);
            check_no_uvars = (uu___111_1551.check_no_uvars);
            unmeta = (uu___111_1551.unmeta);
            unascribe = (uu___111_1551.unascribe);
            in_full_norm_request = (uu___111_1551.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___111_1551.weakly_reduce_scrutinee)
          }
      | Simplify  ->
          let uu___112_1552 = fs  in
          {
            beta = (uu___112_1552.beta);
            iota = (uu___112_1552.iota);
            zeta = (uu___112_1552.zeta);
            weak = (uu___112_1552.weak);
            hnf = (uu___112_1552.hnf);
            primops = (uu___112_1552.primops);
            do_not_unfold_pure_lets = (uu___112_1552.do_not_unfold_pure_lets);
            unfold_until = (uu___112_1552.unfold_until);
            unfold_only = (uu___112_1552.unfold_only);
            unfold_fully = (uu___112_1552.unfold_fully);
            unfold_attr = (uu___112_1552.unfold_attr);
            unfold_tac = (uu___112_1552.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1552.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___112_1552.erase_universes);
            allow_unbound_universes = (uu___112_1552.allow_unbound_universes);
            reify_ = (uu___112_1552.reify_);
            compress_uvars = (uu___112_1552.compress_uvars);
            no_full_norm = (uu___112_1552.no_full_norm);
            check_no_uvars = (uu___112_1552.check_no_uvars);
            unmeta = (uu___112_1552.unmeta);
            unascribe = (uu___112_1552.unascribe);
            in_full_norm_request = (uu___112_1552.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___112_1552.weakly_reduce_scrutinee)
          }
      | EraseUniverses  ->
          let uu___113_1553 = fs  in
          {
            beta = (uu___113_1553.beta);
            iota = (uu___113_1553.iota);
            zeta = (uu___113_1553.zeta);
            weak = (uu___113_1553.weak);
            hnf = (uu___113_1553.hnf);
            primops = (uu___113_1553.primops);
            do_not_unfold_pure_lets = (uu___113_1553.do_not_unfold_pure_lets);
            unfold_until = (uu___113_1553.unfold_until);
            unfold_only = (uu___113_1553.unfold_only);
            unfold_fully = (uu___113_1553.unfold_fully);
            unfold_attr = (uu___113_1553.unfold_attr);
            unfold_tac = (uu___113_1553.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1553.pure_subterms_within_computations);
            simplify = (uu___113_1553.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___113_1553.allow_unbound_universes);
            reify_ = (uu___113_1553.reify_);
            compress_uvars = (uu___113_1553.compress_uvars);
            no_full_norm = (uu___113_1553.no_full_norm);
            check_no_uvars = (uu___113_1553.check_no_uvars);
            unmeta = (uu___113_1553.unmeta);
            unascribe = (uu___113_1553.unascribe);
            in_full_norm_request = (uu___113_1553.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___113_1553.weakly_reduce_scrutinee)
          }
      | AllowUnboundUniverses  ->
          let uu___114_1554 = fs  in
          {
            beta = (uu___114_1554.beta);
            iota = (uu___114_1554.iota);
            zeta = (uu___114_1554.zeta);
            weak = (uu___114_1554.weak);
            hnf = (uu___114_1554.hnf);
            primops = (uu___114_1554.primops);
            do_not_unfold_pure_lets = (uu___114_1554.do_not_unfold_pure_lets);
            unfold_until = (uu___114_1554.unfold_until);
            unfold_only = (uu___114_1554.unfold_only);
            unfold_fully = (uu___114_1554.unfold_fully);
            unfold_attr = (uu___114_1554.unfold_attr);
            unfold_tac = (uu___114_1554.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1554.pure_subterms_within_computations);
            simplify = (uu___114_1554.simplify);
            erase_universes = (uu___114_1554.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___114_1554.reify_);
            compress_uvars = (uu___114_1554.compress_uvars);
            no_full_norm = (uu___114_1554.no_full_norm);
            check_no_uvars = (uu___114_1554.check_no_uvars);
            unmeta = (uu___114_1554.unmeta);
            unascribe = (uu___114_1554.unascribe);
            in_full_norm_request = (uu___114_1554.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___114_1554.weakly_reduce_scrutinee)
          }
      | Reify  ->
          let uu___115_1555 = fs  in
          {
            beta = (uu___115_1555.beta);
            iota = (uu___115_1555.iota);
            zeta = (uu___115_1555.zeta);
            weak = (uu___115_1555.weak);
            hnf = (uu___115_1555.hnf);
            primops = (uu___115_1555.primops);
            do_not_unfold_pure_lets = (uu___115_1555.do_not_unfold_pure_lets);
            unfold_until = (uu___115_1555.unfold_until);
            unfold_only = (uu___115_1555.unfold_only);
            unfold_fully = (uu___115_1555.unfold_fully);
            unfold_attr = (uu___115_1555.unfold_attr);
            unfold_tac = (uu___115_1555.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1555.pure_subterms_within_computations);
            simplify = (uu___115_1555.simplify);
            erase_universes = (uu___115_1555.erase_universes);
            allow_unbound_universes = (uu___115_1555.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___115_1555.compress_uvars);
            no_full_norm = (uu___115_1555.no_full_norm);
            check_no_uvars = (uu___115_1555.check_no_uvars);
            unmeta = (uu___115_1555.unmeta);
            unascribe = (uu___115_1555.unascribe);
            in_full_norm_request = (uu___115_1555.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___115_1555.weakly_reduce_scrutinee)
          }
      | CompressUvars  ->
          let uu___116_1556 = fs  in
          {
            beta = (uu___116_1556.beta);
            iota = (uu___116_1556.iota);
            zeta = (uu___116_1556.zeta);
            weak = (uu___116_1556.weak);
            hnf = (uu___116_1556.hnf);
            primops = (uu___116_1556.primops);
            do_not_unfold_pure_lets = (uu___116_1556.do_not_unfold_pure_lets);
            unfold_until = (uu___116_1556.unfold_until);
            unfold_only = (uu___116_1556.unfold_only);
            unfold_fully = (uu___116_1556.unfold_fully);
            unfold_attr = (uu___116_1556.unfold_attr);
            unfold_tac = (uu___116_1556.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1556.pure_subterms_within_computations);
            simplify = (uu___116_1556.simplify);
            erase_universes = (uu___116_1556.erase_universes);
            allow_unbound_universes = (uu___116_1556.allow_unbound_universes);
            reify_ = (uu___116_1556.reify_);
            compress_uvars = true;
            no_full_norm = (uu___116_1556.no_full_norm);
            check_no_uvars = (uu___116_1556.check_no_uvars);
            unmeta = (uu___116_1556.unmeta);
            unascribe = (uu___116_1556.unascribe);
            in_full_norm_request = (uu___116_1556.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___116_1556.weakly_reduce_scrutinee)
          }
      | NoFullNorm  ->
          let uu___117_1557 = fs  in
          {
            beta = (uu___117_1557.beta);
            iota = (uu___117_1557.iota);
            zeta = (uu___117_1557.zeta);
            weak = (uu___117_1557.weak);
            hnf = (uu___117_1557.hnf);
            primops = (uu___117_1557.primops);
            do_not_unfold_pure_lets = (uu___117_1557.do_not_unfold_pure_lets);
            unfold_until = (uu___117_1557.unfold_until);
            unfold_only = (uu___117_1557.unfold_only);
            unfold_fully = (uu___117_1557.unfold_fully);
            unfold_attr = (uu___117_1557.unfold_attr);
            unfold_tac = (uu___117_1557.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1557.pure_subterms_within_computations);
            simplify = (uu___117_1557.simplify);
            erase_universes = (uu___117_1557.erase_universes);
            allow_unbound_universes = (uu___117_1557.allow_unbound_universes);
            reify_ = (uu___117_1557.reify_);
            compress_uvars = (uu___117_1557.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___117_1557.check_no_uvars);
            unmeta = (uu___117_1557.unmeta);
            unascribe = (uu___117_1557.unascribe);
            in_full_norm_request = (uu___117_1557.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___117_1557.weakly_reduce_scrutinee)
          }
      | CheckNoUvars  ->
          let uu___118_1558 = fs  in
          {
            beta = (uu___118_1558.beta);
            iota = (uu___118_1558.iota);
            zeta = (uu___118_1558.zeta);
            weak = (uu___118_1558.weak);
            hnf = (uu___118_1558.hnf);
            primops = (uu___118_1558.primops);
            do_not_unfold_pure_lets = (uu___118_1558.do_not_unfold_pure_lets);
            unfold_until = (uu___118_1558.unfold_until);
            unfold_only = (uu___118_1558.unfold_only);
            unfold_fully = (uu___118_1558.unfold_fully);
            unfold_attr = (uu___118_1558.unfold_attr);
            unfold_tac = (uu___118_1558.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1558.pure_subterms_within_computations);
            simplify = (uu___118_1558.simplify);
            erase_universes = (uu___118_1558.erase_universes);
            allow_unbound_universes = (uu___118_1558.allow_unbound_universes);
            reify_ = (uu___118_1558.reify_);
            compress_uvars = (uu___118_1558.compress_uvars);
            no_full_norm = (uu___118_1558.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___118_1558.unmeta);
            unascribe = (uu___118_1558.unascribe);
            in_full_norm_request = (uu___118_1558.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___118_1558.weakly_reduce_scrutinee)
          }
      | Unmeta  ->
          let uu___119_1559 = fs  in
          {
            beta = (uu___119_1559.beta);
            iota = (uu___119_1559.iota);
            zeta = (uu___119_1559.zeta);
            weak = (uu___119_1559.weak);
            hnf = (uu___119_1559.hnf);
            primops = (uu___119_1559.primops);
            do_not_unfold_pure_lets = (uu___119_1559.do_not_unfold_pure_lets);
            unfold_until = (uu___119_1559.unfold_until);
            unfold_only = (uu___119_1559.unfold_only);
            unfold_fully = (uu___119_1559.unfold_fully);
            unfold_attr = (uu___119_1559.unfold_attr);
            unfold_tac = (uu___119_1559.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1559.pure_subterms_within_computations);
            simplify = (uu___119_1559.simplify);
            erase_universes = (uu___119_1559.erase_universes);
            allow_unbound_universes = (uu___119_1559.allow_unbound_universes);
            reify_ = (uu___119_1559.reify_);
            compress_uvars = (uu___119_1559.compress_uvars);
            no_full_norm = (uu___119_1559.no_full_norm);
            check_no_uvars = (uu___119_1559.check_no_uvars);
            unmeta = true;
            unascribe = (uu___119_1559.unascribe);
            in_full_norm_request = (uu___119_1559.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___119_1559.weakly_reduce_scrutinee)
          }
      | Unascribe  ->
          let uu___120_1560 = fs  in
          {
            beta = (uu___120_1560.beta);
            iota = (uu___120_1560.iota);
            zeta = (uu___120_1560.zeta);
            weak = (uu___120_1560.weak);
            hnf = (uu___120_1560.hnf);
            primops = (uu___120_1560.primops);
            do_not_unfold_pure_lets = (uu___120_1560.do_not_unfold_pure_lets);
            unfold_until = (uu___120_1560.unfold_until);
            unfold_only = (uu___120_1560.unfold_only);
            unfold_fully = (uu___120_1560.unfold_fully);
            unfold_attr = (uu___120_1560.unfold_attr);
            unfold_tac = (uu___120_1560.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_1560.pure_subterms_within_computations);
            simplify = (uu___120_1560.simplify);
            erase_universes = (uu___120_1560.erase_universes);
            allow_unbound_universes = (uu___120_1560.allow_unbound_universes);
            reify_ = (uu___120_1560.reify_);
            compress_uvars = (uu___120_1560.compress_uvars);
            no_full_norm = (uu___120_1560.no_full_norm);
            check_no_uvars = (uu___120_1560.check_no_uvars);
            unmeta = (uu___120_1560.unmeta);
            unascribe = true;
            in_full_norm_request = (uu___120_1560.in_full_norm_request);
            weakly_reduce_scrutinee = (uu___120_1560.weakly_reduce_scrutinee)
          }
  
let rec to_fsteps : step Prims.list -> fsteps =
  fun s  -> FStar_List.fold_right fstep_add_one s default_steps 
type psc =
  {
  psc_range: FStar_Range.range ;
  psc_subst: unit -> FStar_Syntax_Syntax.subst_t }[@@deriving show]
let __proj__Mkpsc__item__psc_range : psc -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
  
let __proj__Mkpsc__item__psc_subst :
  psc -> unit -> FStar_Syntax_Syntax.subst_t =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
  
let null_psc : psc =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1613  -> []) } 
let psc_range : psc -> FStar_Range.range = fun psc  -> psc.psc_range 
let psc_subst : psc -> FStar_Syntax_Syntax.subst_t =
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
let __proj__Mkprimitive_step__item__name : primitive_step -> FStar_Ident.lid
  =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__name
  
let __proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__arity
  
let __proj__Mkprimitive_step__item__auto_reflect :
  primitive_step -> Prims.int FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__auto_reflect
  
let __proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
  
let __proj__Mkprimitive_step__item__requires_binder_substitution :
  primitive_step -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        auto_reflect = __fname__auto_reflect;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__requires_binder_substitution
  
let __proj__Mkprimitive_step__item__interpretation :
  primitive_step ->
    psc ->
      FStar_Syntax_Syntax.args ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
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
let uu___is_Clos : closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____1902 -> false
  
let __proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
      ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let uu___is_Univ : closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____2006 -> false
  
let __proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let uu___is_Dummy : closure -> Prims.bool =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____2019 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2
  = (FStar_Pervasives_Native.None, Dummy) 
type debug_switches =
  {
  gen: Prims.bool ;
  primop: Prims.bool ;
  b380: Prims.bool ;
  norm_delayed: Prims.bool ;
  print_normalized: Prims.bool }[@@deriving show]
let __proj__Mkdebug_switches__item__gen : debug_switches -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__gen
  
let __proj__Mkdebug_switches__item__primop : debug_switches -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__primop
  
let __proj__Mkdebug_switches__item__b380 : debug_switches -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} -> __fname__b380
  
let __proj__Mkdebug_switches__item__norm_delayed :
  debug_switches -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380;
        norm_delayed = __fname__norm_delayed;
        print_normalized = __fname__print_normalized;_} ->
        __fname__norm_delayed
  
let __proj__Mkdebug_switches__item__print_normalized :
  debug_switches -> Prims.bool =
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
let __proj__Mkcfg__item__steps : cfg -> fsteps =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__steps
  
let __proj__Mkcfg__item__tcenv : cfg -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__tcenv
  
let __proj__Mkcfg__item__debug : cfg -> debug_switches =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__debug
  
let __proj__Mkcfg__item__delta_level :
  cfg -> FStar_TypeChecker_Env.delta_level Prims.list =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__delta_level
  
let __proj__Mkcfg__item__primitive_steps :
  cfg -> primitive_step FStar_Util.psmap =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__primitive_steps
  
let __proj__Mkcfg__item__strong : cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__strong
  
let __proj__Mkcfg__item__memoize_lazy : cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__memoize_lazy
  
let __proj__Mkcfg__item__normalize_pure_lets : cfg -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { steps = __fname__steps; tcenv = __fname__tcenv;
        debug = __fname__debug; delta_level = __fname__delta_level;
        primitive_steps = __fname__primitive_steps; strong = __fname__strong;
        memoize_lazy = __fname__memoize_lazy;
        normalize_pure_lets = __fname__normalize_pure_lets;_} ->
        __fname__normalize_pure_lets
  
let add_steps :
  primitive_step FStar_Util.psmap ->
    primitive_step Prims.list -> primitive_step FStar_Util.psmap
  =
  fun m  ->
    fun l  ->
      FStar_List.fold_right
        (fun p  ->
           fun m1  ->
             let uu____2330 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____2330 p) l m
  
let prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap =
  fun l  ->
    let uu____2344 = FStar_Util.psmap_empty ()  in add_steps uu____2344 l
  
let find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option
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
let uu___is_Arg : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____2517 -> false
  
let __proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let uu___is_UnivArgs : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2555 -> false
  
let __proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let uu___is_MemoLazy : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2593 -> false
  
let __proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let uu___is_Match : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2666 -> false
  
let __proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Match _0 -> _0 
let uu___is_Abs : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2716 -> false
  
let __proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let uu___is_App : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2774 -> false
  
let __proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | App _0 -> _0 
let uu___is_Meta : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2818 -> false
  
let __proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let uu___is_Let : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2858 -> false
  
let __proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Let _0 -> _0 
let uu___is_Cfg : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2896 -> false
  
let __proj__Cfg__item___0 : stack_elt -> cfg =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let uu___is_Debug : stack_elt -> Prims.bool =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2914 -> false
  
let __proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
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
  
let rec env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string
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

and closure_to_string : closure -> Prims.string =
  fun uu___79_3201  ->
    match uu___79_3201 with
    | Clos (env,t,uu____3204,uu____3205) ->
        let uu____3250 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____3257 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____3250 uu____3257
    | Univ uu____3258 -> "Univ"
    | Dummy  -> "dummy"

let stack_elt_to_string : stack_elt -> Prims.string =
  fun uu___80_3263  ->
    match uu___80_3263 with
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
  
let stack_to_string : stack_elt Prims.list -> Prims.string =
  fun s  ->
    let uu____3335 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____3335 (FStar_String.concat "; ")
  
let log : cfg -> (unit -> unit) -> unit =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let log_primops : cfg -> (unit -> unit) -> unit =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____3376 . 'Auu____3376 Prims.list -> Prims.bool =
  fun uu___81_3383  ->
    match uu___81_3383 with | [] -> true | uu____3386 -> false
  
let lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure
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
  
let downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option =
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
  
let norm_universe :
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
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
  
let rec inline_closure_env :
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____3861  ->
               let uu____3862 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3863 = env_to_string env  in
               let uu____3864 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3862 uu____3863 uu____3864);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3873 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3876 ->
                    let uu____3901 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3901
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3902 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3903 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3904 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3905 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar uu____3906 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3928 ->
                           let uu____3945 =
                             let uu____3946 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____3947 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____3946 uu____3947
                              in
                           failwith uu____3945
                       | uu____3950 -> inline_closure_env cfg env stack t1)
                    else rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____3956 =
                        let uu____3957 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____3957  in
                      mk uu____3956 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____3965 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3965  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____3967 = lookup_bvar env x  in
                    (match uu____3967 with
                     | Univ uu____3970 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___125_3974 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___125_3974.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___125_3974.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____3980,uu____3981) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____4066  ->
                              fun stack1  ->
                                match uu____4066 with
                                | (a,aq) ->
                                    let uu____4078 =
                                      let uu____4079 =
                                        let uu____4086 =
                                          let uu____4087 =
                                            let uu____4118 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____4118, false)  in
                                          Clos uu____4087  in
                                        (uu____4086, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____4079  in
                                    uu____4078 :: stack1) args)
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
                    let uu____4312 = close_binders cfg env bs  in
                    (match uu____4312 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4359 =
                      let uu____4370 =
                        let uu____4377 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4377]  in
                      close_binders cfg env uu____4370  in
                    (match uu____4359 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4400 =
                             let uu____4401 =
                               let uu____4408 =
                                 let uu____4409 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4409
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4408, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4401  in
                           mk uu____4400 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4500 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4500
                      | FStar_Util.Inr c ->
                          let uu____4514 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4514
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4533 =
                        let uu____4534 =
                          let uu____4561 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4561, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4534  in
                      mk uu____4533 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4607 =
                            let uu____4608 =
                              let uu____4615 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4615, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4608  in
                          mk uu____4607 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4667  -> dummy :: env1) env
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
                    let uu____4688 =
                      let uu____4699 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____4699
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____4718 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___126_4734 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___126_4734.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___126_4734.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____4718))
                       in
                    (match uu____4688 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___127_4752 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___127_4752.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___127_4752.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___127_4752.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___127_4752.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____4766,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4829  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4854 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4854
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4874  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4898 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4898
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___128_4906 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___128_4906.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___128_4906.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___129_4907 = lb  in
                      let uu____4908 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___129_4907.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___129_4907.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4908;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___129_4907.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___129_4907.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____4940  -> fun env1  -> dummy :: env1)
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

and non_tail_inline_closure_env :
  cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun cfg  -> fun env  -> fun t  -> inline_closure_env cfg env [] t

and rebuild_closure :
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____5043  ->
               let uu____5044 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5045 = env_to_string env  in
               let uu____5046 = stack_to_string stack  in
               let uu____5047 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5044 uu____5045 uu____5046 uu____5047);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5052,uu____5053),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____5128 = close_binders cfg env' bs  in
               (match uu____5128 with
                | (bs1,uu____5142) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____5158 =
                      let uu___130_5159 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___130_5159.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___130_5159.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____5158)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____5205 =
                 match uu____5205 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____5280 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____5301 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____5361  ->
                                     fun uu____5362  ->
                                       match (uu____5361, uu____5362) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____5453 = norm_pat env4 p1
                                              in
                                           (match uu____5453 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____5301 with
                            | (pats1,env4) ->
                                ((let uu___131_5535 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___131_5535.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___132_5554 = x  in
                             let uu____5555 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___132_5554.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___132_5554.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5555
                             }  in
                           ((let uu___133_5569 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___133_5569.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___134_5580 = x  in
                             let uu____5581 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___134_5580.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___134_5580.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5581
                             }  in
                           ((let uu___135_5595 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___135_5595.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___136_5611 = x  in
                             let uu____5612 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___136_5611.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___136_5611.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____5612
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___137_5621 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___137_5621.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____5626 = norm_pat env2 pat  in
                     (match uu____5626 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____5671 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____5671
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____5690 =
                   let uu____5691 =
                     let uu____5714 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____5714)  in
                   FStar_Syntax_Syntax.Tm_match uu____5691  in
                 mk uu____5690 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____5809 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____5898  ->
                                       match uu____5898 with
                                       | (a,q) ->
                                           let uu____5917 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____5917, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____5809
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____5928 =
                       let uu____5935 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____5935)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____5928
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____5947 =
                       let uu____5956 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____5956)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____5947
                 | uu____5961 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____5965 -> failwith "Impossible: unexpected stack element")

and close_binders :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list,env)
          FStar_Pervasives_Native.tuple2
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____5979 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____6028  ->
                  fun uu____6029  ->
                    match (uu____6028, uu____6029) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___138_6099 = b  in
                          let uu____6100 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___138_6099.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___138_6099.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____6100
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____5979 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

and close_comp :
  cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> c
        | uu____6193 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____6206 = inline_closure_env cfg env [] t  in
                 let uu____6207 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____6206 uu____6207
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____6220 = inline_closure_env cfg env [] t  in
                 let uu____6221 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____6220 uu____6221
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____6267  ->
                           match uu____6267 with
                           | (a,q) ->
                               let uu____6280 =
                                 inline_closure_env cfg env [] a  in
                               (uu____6280, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___82_6295  ->
                           match uu___82_6295 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____6299 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____6299
                           | f -> f))
                    in
                 let uu____6303 =
                   let uu___139_6304 = c1  in
                   let uu____6305 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____6305;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___139_6304.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____6303)

and filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___83_6315  ->
            match uu___83_6315 with
            | FStar_Syntax_Syntax.DECREASES uu____6316 -> false
            | uu____6319 -> true))

and close_lcomp_opt :
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___84_6337  ->
                      match uu___84_6337 with
                      | FStar_Syntax_Syntax.DECREASES uu____6338 -> false
                      | uu____6341 -> true))
               in
            let rc1 =
              let uu___140_6343 = rc  in
              let uu____6344 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___140_6343.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____6344;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____6353 -> lopt

let closure_as_term :
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun cfg  -> fun env  -> fun t  -> non_tail_inline_closure_env cfg env t 
let built_in_primitive_steps : primitive_step FStar_Util.psmap =
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
    let uu____6466 =
      let uu____6475 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____6475  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6466  in
  let arg_as_bounded_int uu____6501 =
    match uu____6501 with
    | (a,uu____6513) ->
        let uu____6520 =
          let uu____6521 = FStar_Syntax_Subst.compress a  in
          uu____6521.FStar_Syntax_Syntax.n  in
        (match uu____6520 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____6531;
                FStar_Syntax_Syntax.vars = uu____6532;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____6534;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____6535;_},uu____6536)::[])
             when
             let uu____6575 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6575 "int_to_t" ->
             let uu____6576 =
               let uu____6581 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____6581)  in
             FStar_Pervasives_Native.Some uu____6576
         | uu____6586 -> FStar_Pervasives_Native.None)
     in
  let lift_unary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____6634 = f a  in FStar_Pervasives_Native.Some uu____6634
    | uu____6635 -> FStar_Pervasives_Native.None  in
  let lift_binary f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____6691 = f a0 a1  in FStar_Pervasives_Native.Some uu____6691
    | uu____6692 -> FStar_Pervasives_Native.None  in
  let unary_op as_a f res args =
    let uu____6750 = FStar_List.map as_a args  in
    lift_unary (f res.psc_range) uu____6750  in
  let binary_op as_a f res args =
    let uu____6815 = FStar_List.map as_a args  in
    lift_binary (f res.psc_range) uu____6815  in
  let as_primitive_step is_strong uu____6846 =
    match uu____6846 with
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
           let uu____6906 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
             uu____6906)
     in
  let binary_int_op f =
    binary_op arg_as_int
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____6942 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r
               uu____6942)
     in
  let unary_bool_op f =
    unary_op arg_as_bool
      (fun r  ->
         fun x  ->
           let uu____6971 = f x  in
           FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
             uu____6971)
     in
  let binary_bool_op f =
    binary_op arg_as_bool
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7007 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r
               uu____7007)
     in
  let binary_string_op f =
    binary_op arg_as_string
      (fun r  ->
         fun x  ->
           fun y  ->
             let uu____7043 = f x y  in
             FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r
               uu____7043)
     in
  let mixed_binary_op as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____7175 =
          let uu____7184 = as_a a  in
          let uu____7187 = as_b b  in (uu____7184, uu____7187)  in
        (match uu____7175 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____7202 =
               let uu____7203 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____7203  in
             FStar_Pervasives_Native.Some uu____7202
         | uu____7204 -> FStar_Pervasives_Native.None)
    | uu____7213 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____7233 =
        let uu____7234 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____7234  in
      mk uu____7233 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____7246 =
      let uu____7249 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____7249  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7246  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____7291 =
      let uu____7292 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____7292  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____7291
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____7314 = arg_as_string a1  in
        (match uu____7314 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7320 = arg_as_list FStar_Syntax_Embeddings.e_string a2
                in
             (match uu____7320 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7333 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____7333
              | uu____7334 -> FStar_Pervasives_Native.None)
         | uu____7339 -> FStar_Pervasives_Native.None)
    | uu____7342 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____7356 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____7356
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7393 =
          let uu____7414 = arg_as_string fn  in
          let uu____7417 = arg_as_int from_line  in
          let uu____7420 = arg_as_int from_col  in
          let uu____7423 = arg_as_int to_line  in
          let uu____7426 = arg_as_int to_col  in
          (uu____7414, uu____7417, uu____7420, uu____7423, uu____7426)  in
        (match uu____7393 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7457 =
                 let uu____7458 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7459 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7458 uu____7459  in
               let uu____7460 =
                 let uu____7461 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7462 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7461 uu____7462  in
               FStar_Range.mk_range fn1 uu____7457 uu____7460  in
             let uu____7463 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7463
         | uu____7464 -> FStar_Pervasives_Native.None)
    | uu____7485 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____7518)::(a1,uu____7520)::(a2,uu____7522)::[] ->
        let uu____7559 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7559 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____7572 -> FStar_Pervasives_Native.None)
    | uu____7573 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____7604)::[] ->
        let uu____7613 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____7613 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7619 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____7619
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7620 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____7646 =
      let uu____7663 =
        let uu____7680 =
          let uu____7697 =
            let uu____7714 =
              let uu____7731 =
                let uu____7748 =
                  let uu____7765 =
                    let uu____7782 =
                      let uu____7799 =
                        let uu____7816 =
                          let uu____7833 =
                            let uu____7850 =
                              let uu____7867 =
                                let uu____7884 =
                                  let uu____7901 =
                                    let uu____7918 =
                                      let uu____7935 =
                                        let uu____7952 =
                                          let uu____7969 =
                                            let uu____7986 =
                                              let uu____8003 =
                                                let uu____8018 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____8018,
                                                  (Prims.lift_native_int (1)),
                                                  (unary_op arg_as_string
                                                     list_of_string'))
                                                 in
                                              let uu____8027 =
                                                let uu____8044 =
                                                  let uu____8059 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____8059,
                                                    (Prims.lift_native_int (1)),
                                                    (unary_op
                                                       (arg_as_list
                                                          FStar_Syntax_Embeddings.e_char)
                                                       string_of_list'))
                                                   in
                                                let uu____8072 =
                                                  let uu____8089 =
                                                    let uu____8106 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____8106,
                                                      (Prims.lift_native_int (2)),
                                                      string_concat')
                                                     in
                                                  let uu____8117 =
                                                    let uu____8136 =
                                                      let uu____8153 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____8153,
                                                        (Prims.lift_native_int (5)),
                                                        mk_range1)
                                                       in
                                                    [uu____8136]  in
                                                  uu____8089 :: uu____8117
                                                   in
                                                uu____8044 :: uu____8072  in
                                              uu____8003 :: uu____8027  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.lift_native_int (3)),
                                              (decidable_eq true)) ::
                                              uu____7986
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.lift_native_int (3)),
                                            (decidable_eq false)) ::
                                            uu____7969
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.lift_native_int (2)),
                                          (binary_op arg_as_string
                                             string_compare'))
                                          :: uu____7952
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.lift_native_int (1)),
                                        (unary_op arg_as_bool string_of_bool1))
                                        :: uu____7935
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.lift_native_int (1)),
                                      (unary_op arg_as_int string_of_int1))
                                      :: uu____7918
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.lift_native_int (2)),
                                    (mixed_binary_op arg_as_int arg_as_char
                                       (FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_string)
                                       (fun r  ->
                                          fun x  ->
                                            fun y  ->
                                              let uu____8381 =
                                                FStar_BigInt.to_int_fs x  in
                                              FStar_String.make uu____8381 y)))
                                    :: uu____7901
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.lift_native_int (2)),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____7884
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.lift_native_int (2)),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____7867
                               in
                            (FStar_Parser_Const.op_Or,
                              (Prims.lift_native_int (2)),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____7850
                             in
                          (FStar_Parser_Const.op_And,
                            (Prims.lift_native_int (2)),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____7833
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.lift_native_int (1)),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____7816
                         in
                      (FStar_Parser_Const.op_Modulus,
                        (Prims.lift_native_int (2)),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____7799
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.lift_native_int (2)),
                      (binary_op arg_as_int
                         (fun r  ->
                            fun x  ->
                              fun y  ->
                                let uu____8576 = FStar_BigInt.ge_big_int x y
                                   in
                                FStar_Syntax_Embeddings.embed
                                  FStar_Syntax_Embeddings.e_bool r uu____8576)))
                      :: uu____7782
                     in
                  (FStar_Parser_Const.op_GT, (Prims.lift_native_int (2)),
                    (binary_op arg_as_int
                       (fun r  ->
                          fun x  ->
                            fun y  ->
                              let uu____8606 = FStar_BigInt.gt_big_int x y
                                 in
                              FStar_Syntax_Embeddings.embed
                                FStar_Syntax_Embeddings.e_bool r uu____8606)))
                    :: uu____7765
                   in
                (FStar_Parser_Const.op_LTE, (Prims.lift_native_int (2)),
                  (binary_op arg_as_int
                     (fun r  ->
                        fun x  ->
                          fun y  ->
                            let uu____8636 = FStar_BigInt.le_big_int x y  in
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_bool r uu____8636)))
                  :: uu____7748
                 in
              (FStar_Parser_Const.op_LT, (Prims.lift_native_int (2)),
                (binary_op arg_as_int
                   (fun r  ->
                      fun x  ->
                        fun y  ->
                          let uu____8666 = FStar_BigInt.lt_big_int x y  in
                          FStar_Syntax_Embeddings.embed
                            FStar_Syntax_Embeddings.e_bool r uu____8666)))
                :: uu____7731
               in
            (FStar_Parser_Const.op_Division, (Prims.lift_native_int (2)),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____7714
             in
          (FStar_Parser_Const.op_Multiply, (Prims.lift_native_int (2)),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____7697
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.lift_native_int (2)),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____7680
         in
      (FStar_Parser_Const.op_Addition, (Prims.lift_native_int (2)),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____7663
       in
    (FStar_Parser_Const.op_Minus, (Prims.lift_native_int (1)),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____7646
     in
  let weak_ops =
    let uu____8827 =
      let uu____8848 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____8848, (Prims.lift_native_int (1)), prims_to_fstar_range_step)
       in
    [uu____8827]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____8946 =
        let uu____8951 =
          let uu____8952 = FStar_Syntax_Syntax.as_arg c  in [uu____8952]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____8951  in
      uu____8946 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____9008 =
                let uu____9023 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____9023, (Prims.lift_native_int (2)),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9045  ->
                          fun uu____9046  ->
                            match (uu____9045, uu____9046) with
                            | ((int_to_t1,x),(uu____9065,y)) ->
                                let uu____9075 = FStar_BigInt.add_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9075)))
                 in
              let uu____9076 =
                let uu____9093 =
                  let uu____9108 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____9108, (Prims.lift_native_int (2)),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9130  ->
                            fun uu____9131  ->
                              match (uu____9130, uu____9131) with
                              | ((int_to_t1,x),(uu____9150,y)) ->
                                  let uu____9160 =
                                    FStar_BigInt.sub_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9160)))
                   in
                let uu____9161 =
                  let uu____9178 =
                    let uu____9193 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____9193, (Prims.lift_native_int (2)),
                      (binary_op arg_as_bounded_int
                         (fun r  ->
                            fun uu____9215  ->
                              fun uu____9216  ->
                                match (uu____9215, uu____9216) with
                                | ((int_to_t1,x),(uu____9235,y)) ->
                                    let uu____9245 =
                                      FStar_BigInt.mult_big_int x y  in
                                    int_as_bounded r int_to_t1 uu____9245)))
                     in
                  let uu____9246 =
                    let uu____9263 =
                      let uu____9278 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____9278, (Prims.lift_native_int (1)),
                        (unary_op arg_as_bounded_int
                           (fun r  ->
                              fun uu____9296  ->
                                match uu____9296 with
                                | (int_to_t1,x) ->
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_int r x)))
                       in
                    [uu____9263]  in
                  uu____9178 :: uu____9246  in
                uu____9093 :: uu____9161  in
              uu____9008 :: uu____9076))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____9426 =
                let uu____9441 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____9441, (Prims.lift_native_int (2)),
                  (binary_op arg_as_bounded_int
                     (fun r  ->
                        fun uu____9463  ->
                          fun uu____9464  ->
                            match (uu____9463, uu____9464) with
                            | ((int_to_t1,x),(uu____9483,y)) ->
                                let uu____9493 = FStar_BigInt.div_big_int x y
                                   in
                                int_as_bounded r int_to_t1 uu____9493)))
                 in
              let uu____9494 =
                let uu____9511 =
                  let uu____9526 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____9526, (Prims.lift_native_int (2)),
                    (binary_op arg_as_bounded_int
                       (fun r  ->
                          fun uu____9548  ->
                            fun uu____9549  ->
                              match (uu____9548, uu____9549) with
                              | ((int_to_t1,x),(uu____9568,y)) ->
                                  let uu____9578 =
                                    FStar_BigInt.mod_big_int x y  in
                                  int_as_bounded r int_to_t1 uu____9578)))
                   in
                [uu____9511]  in
              uu____9426 :: uu____9494))
       in
    FStar_List.append add_sub_mul_v div_mod_unsigned  in
  let strong_steps =
    FStar_List.map (as_primitive_step true)
      (FStar_List.append basic_ops bounded_arith_ops)
     in
  let weak_steps = FStar_List.map (as_primitive_step false) weak_ops  in
  FStar_All.pipe_left prim_from_list
    (FStar_List.append strong_steps weak_steps)
  
let equality_ops : primitive_step FStar_Util.psmap =
  let interp_prop psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____9708)::(a1,uu____9710)::(a2,uu____9712)::[] ->
        let uu____9749 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9749 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___141_9755 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_9755.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_9755.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___142_9759 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___142_9759.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___142_9759.FStar_Syntax_Syntax.vars)
                })
         | uu____9760 -> FStar_Pervasives_Native.None)
    | (_typ,uu____9762)::uu____9763::(a1,uu____9765)::(a2,uu____9767)::[] ->
        let uu____9816 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____9816 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___141_9822 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_9822.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_9822.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___142_9826 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___142_9826.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___142_9826.FStar_Syntax_Syntax.vars)
                })
         | uu____9827 -> FStar_Pervasives_Native.None)
    | uu____9828 -> failwith "Unexpected number of arguments"  in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.lift_native_int (3));
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.lift_native_int (4));
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  prim_from_list [propositional_equality; hetero_propositional_equality] 
let unembed_binder_knot :
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option
  =
  fun t  ->
    let uu____9882 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____9882 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____9934 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9934) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____9996  ->
           fun subst1  ->
             match uu____9996 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____10037,uu____10038)) ->
                      let uu____10097 = b  in
                      (match uu____10097 with
                       | (bv,uu____10105) ->
                           let uu____10106 =
                             let uu____10107 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____10107  in
                           if uu____10106
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____10112 = unembed_binder term1  in
                              match uu____10112 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____10119 =
                                      let uu___143_10120 = bv  in
                                      let uu____10121 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___143_10120.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___143_10120.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____10121
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____10119
                                     in
                                  let b_for_x =
                                    let uu____10125 =
                                      let uu____10132 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____10132)
                                       in
                                    FStar_Syntax_Syntax.NT uu____10125  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___85_10142  ->
                                         match uu___85_10142 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____10143,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____10145;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____10146;_})
                                             ->
                                             let uu____10151 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____10151
                                         | uu____10152 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____10153 -> subst1)) env []
  
let reduce_primops :
  'Auu____10176 'Auu____10177 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10176) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10177 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____10223 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10223 with
             | (head1,args) ->
                 let uu____10260 =
                   let uu____10261 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10261.FStar_Syntax_Syntax.n  in
                 (match uu____10260 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10265 = find_prim_step cfg fv  in
                      (match uu____10265 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____10287  ->
                                   let uu____10288 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____10289 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10296 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10288 uu____10289 uu____10296);
                              tm)
                           else
                             (let uu____10298 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____10298 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____10409  ->
                                        let uu____10410 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10410);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____10413  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____10415 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____10415 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____10421  ->
                                              let uu____10422 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10422);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____10428  ->
                                              let uu____10429 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10430 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10429 uu____10430);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10431 ->
                           (log_primops cfg
                              (fun uu____10435  ->
                                 let uu____10436 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10436);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10440  ->
                            let uu____10441 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10441);
                       (match args with
                        | (a1,uu____10443)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____10460 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____10472  ->
                            let uu____10473 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10473);
                       (match args with
                        | (t,uu____10475)::(r,uu____10477)::[] ->
                            let uu____10504 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____10504 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___144_10508 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___144_10508.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___144_10508.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____10511 -> tm))
                  | uu____10520 -> tm))
  
let reduce_equality :
  'Auu____10531 'Auu____10532 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____10531) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____10532 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___145_10576 = cfg  in
         {
           steps =
             (let uu___146_10579 = default_steps  in
              {
                beta = (uu___146_10579.beta);
                iota = (uu___146_10579.iota);
                zeta = (uu___146_10579.zeta);
                weak = (uu___146_10579.weak);
                hnf = (uu___146_10579.hnf);
                primops = true;
                do_not_unfold_pure_lets =
                  (uu___146_10579.do_not_unfold_pure_lets);
                unfold_until = (uu___146_10579.unfold_until);
                unfold_only = (uu___146_10579.unfold_only);
                unfold_fully = (uu___146_10579.unfold_fully);
                unfold_attr = (uu___146_10579.unfold_attr);
                unfold_tac = (uu___146_10579.unfold_tac);
                pure_subterms_within_computations =
                  (uu___146_10579.pure_subterms_within_computations);
                simplify = (uu___146_10579.simplify);
                erase_universes = (uu___146_10579.erase_universes);
                allow_unbound_universes =
                  (uu___146_10579.allow_unbound_universes);
                reify_ = (uu___146_10579.reify_);
                compress_uvars = (uu___146_10579.compress_uvars);
                no_full_norm = (uu___146_10579.no_full_norm);
                check_no_uvars = (uu___146_10579.check_no_uvars);
                unmeta = (uu___146_10579.unmeta);
                unascribe = (uu___146_10579.unascribe);
                in_full_norm_request = (uu___146_10579.in_full_norm_request);
                weakly_reduce_scrutinee =
                  (uu___146_10579.weakly_reduce_scrutinee)
              });
           tcenv = (uu___145_10576.tcenv);
           debug = (uu___145_10576.debug);
           delta_level = (uu___145_10576.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___145_10576.strong);
           memoize_lazy = (uu___145_10576.memoize_lazy);
           normalize_pure_lets = (uu___145_10576.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____10586 .
    FStar_Syntax_Syntax.term -> 'Auu____10586 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____10601 =
        let uu____10608 =
          let uu____10609 = FStar_Syntax_Util.un_uinst hd1  in
          uu____10609.FStar_Syntax_Syntax.n  in
        (uu____10608, args)  in
      match uu____10601 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10615::uu____10616::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____10620::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____10625::uu____10626::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____10629 -> false
  
let tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list =
  fun uu___86_10642  ->
    match uu___86_10642 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____10648 =
          let uu____10651 =
            let uu____10652 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____10652  in
          [uu____10651]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10648
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____10658 =
          let uu____10661 =
            let uu____10662 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldFully uu____10662  in
          [uu____10661]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____10658
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____10683 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____10683) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____10729 =
          let uu____10734 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____10734 s  in
        match uu____10729 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____10750 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____10750
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____10767::(tm,uu____10769)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____10798)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____10819)::uu____10820::(tm,uu____10822)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____10863 =
            let uu____10868 = full_norm steps  in parse_steps uu____10868  in
          (match uu____10863 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____10907 -> FStar_Pervasives_Native.None
  
let is_reify_head : stack_elt Prims.list -> Prims.bool =
  fun uu___87_10926  ->
    match uu___87_10926 with
    | (App
        (uu____10929,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____10930;
                       FStar_Syntax_Syntax.vars = uu____10931;_},uu____10932,uu____10933))::uu____10934
        -> true
    | uu____10941 -> false
  
let firstn :
  'Auu____10950 .
    Prims.int ->
      'Auu____10950 Prims.list ->
        ('Auu____10950 Prims.list,'Auu____10950 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let should_reify : cfg -> stack_elt Prims.list -> Prims.bool =
  fun cfg  ->
    fun stack  ->
      match stack with
      | (App
          (uu____10992,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____10993;
                         FStar_Syntax_Syntax.vars = uu____10994;_},uu____10995,uu____10996))::uu____10997
          -> (cfg.steps).reify_
      | uu____11004 -> false
  
let rec maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____11027) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____11037) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____11056  ->
                  match uu____11056 with
                  | (a,uu____11064) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____11070 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____11095 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____11096 -> false
    | FStar_Syntax_Syntax.Tm_type uu____11113 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____11114 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____11115 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____11116 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____11117 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____11118 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____11125 -> false
    | FStar_Syntax_Syntax.Tm_let uu____11132 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____11145 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____11162 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____11175 -> true
    | FStar_Syntax_Syntax.Tm_match uu____11182 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____11244  ->
                   match uu____11244 with
                   | (a,uu____11252) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____11259) ->
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
                     (fun uu____11381  ->
                        match uu____11381 with
                        | (a,uu____11389) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____11394,uu____11395,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____11401,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____11407 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____11414 -> false
            | FStar_Syntax_Syntax.Meta_named uu____11415 -> false))
  
let rec norm :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 =
            if (cfg.debug).norm_delayed
            then
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____11707 ->
                   let uu____11732 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____11732
               | uu____11733 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____11741  ->
               let uu____11742 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____11743 = FStar_Syntax_Print.term_to_string t1  in
               let uu____11744 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____11751 =
                 let uu____11752 =
                   let uu____11755 = firstn (Prims.lift_native_int (4)) stack
                      in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11755
                    in
                 stack_to_string uu____11752  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____11742 uu____11743 uu____11744 uu____11751);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____11778 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____11779 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____11780 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11781;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____11782;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11785;
                 FStar_Syntax_Syntax.fv_delta = uu____11786;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____11787;
                 FStar_Syntax_Syntax.fv_delta = uu____11788;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____11789);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____11796 ->
               let uu____11803 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____11803
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____11833 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____11833)
               ->
               let cfg' =
                 let uu___147_11835 = cfg  in
                 {
                   steps =
                     (let uu___148_11838 = cfg.steps  in
                      {
                        beta = (uu___148_11838.beta);
                        iota = (uu___148_11838.iota);
                        zeta = (uu___148_11838.zeta);
                        weak = (uu___148_11838.weak);
                        hnf = (uu___148_11838.hnf);
                        primops = (uu___148_11838.primops);
                        do_not_unfold_pure_lets = false;
                        unfold_until = (uu___148_11838.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___148_11838.unfold_attr);
                        unfold_tac = (uu___148_11838.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___148_11838.pure_subterms_within_computations);
                        simplify = (uu___148_11838.simplify);
                        erase_universes = (uu___148_11838.erase_universes);
                        allow_unbound_universes =
                          (uu___148_11838.allow_unbound_universes);
                        reify_ = (uu___148_11838.reify_);
                        compress_uvars = (uu___148_11838.compress_uvars);
                        no_full_norm = (uu___148_11838.no_full_norm);
                        check_no_uvars = (uu___148_11838.check_no_uvars);
                        unmeta = (uu___148_11838.unmeta);
                        unascribe = (uu___148_11838.unascribe);
                        in_full_norm_request =
                          (uu___148_11838.in_full_norm_request);
                        weakly_reduce_scrutinee =
                          (uu___148_11838.weakly_reduce_scrutinee)
                      });
                   tcenv = (uu___147_11835.tcenv);
                   debug = (uu___147_11835.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___147_11835.primitive_steps);
                   strong = (uu___147_11835.strong);
                   memoize_lazy = (uu___147_11835.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____11843 = get_norm_request (norm cfg' env []) args  in
               (match uu____11843 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____11874  ->
                              fun stack1  ->
                                match uu____11874 with
                                | (a,aq) ->
                                    let uu____11886 =
                                      let uu____11887 =
                                        let uu____11894 =
                                          let uu____11895 =
                                            let uu____11926 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____11926, false)  in
                                          Clos uu____11895  in
                                        (uu____11894, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11887  in
                                    uu____11886 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____12010  ->
                          let uu____12011 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12011);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____12033 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___88_12038  ->
                                match uu___88_12038 with
                                | UnfoldUntil uu____12039 -> true
                                | UnfoldOnly uu____12040 -> true
                                | UnfoldFully uu____12043 -> true
                                | uu____12046 -> false))
                         in
                      if uu____12033
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___149_12051 = cfg  in
                      let uu____12052 =
                        let uu___150_12053 = to_fsteps s  in
                        {
                          beta = (uu___150_12053.beta);
                          iota = (uu___150_12053.iota);
                          zeta = (uu___150_12053.zeta);
                          weak = (uu___150_12053.weak);
                          hnf = (uu___150_12053.hnf);
                          primops = (uu___150_12053.primops);
                          do_not_unfold_pure_lets =
                            (uu___150_12053.do_not_unfold_pure_lets);
                          unfold_until = (uu___150_12053.unfold_until);
                          unfold_only = (uu___150_12053.unfold_only);
                          unfold_fully = (uu___150_12053.unfold_fully);
                          unfold_attr = (uu___150_12053.unfold_attr);
                          unfold_tac = (uu___150_12053.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___150_12053.pure_subterms_within_computations);
                          simplify = (uu___150_12053.simplify);
                          erase_universes = (uu___150_12053.erase_universes);
                          allow_unbound_universes =
                            (uu___150_12053.allow_unbound_universes);
                          reify_ = (uu___150_12053.reify_);
                          compress_uvars = (uu___150_12053.compress_uvars);
                          no_full_norm = (uu___150_12053.no_full_norm);
                          check_no_uvars = (uu___150_12053.check_no_uvars);
                          unmeta = (uu___150_12053.unmeta);
                          unascribe = (uu___150_12053.unascribe);
                          in_full_norm_request = true;
                          weakly_reduce_scrutinee =
                            (uu___150_12053.weakly_reduce_scrutinee)
                        }  in
                      {
                        steps = uu____12052;
                        tcenv = (uu___149_12051.tcenv);
                        debug = (uu___149_12051.debug);
                        delta_level;
                        primitive_steps = (uu___149_12051.primitive_steps);
                        strong = (uu___149_12051.strong);
                        memoize_lazy = (uu___149_12051.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____12062 =
                          let uu____12063 =
                            let uu____12068 = FStar_Util.now ()  in
                            (t1, uu____12068)  in
                          Debug uu____12063  in
                        uu____12062 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____12072 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12072
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____12081 =
                      let uu____12088 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____12088, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____12081  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____12098 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12098  in
               let uu____12099 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____12099
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____12105  ->
                       let uu____12106 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____12107 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____12106 uu____12107);
                  if b
                  then
                    (let uu____12108 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____12108 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    ((let uu____12116 = find_prim_step cfg fv  in
                      FStar_Option.isNone uu____12116) &&
                       (match qninfo with
                        | FStar_Pervasives_Native.Some
                            (FStar_Util.Inr
                             ({
                                FStar_Syntax_Syntax.sigel =
                                  FStar_Syntax_Syntax.Sig_let
                                  ((is_rec,uu____12129),uu____12130);
                                FStar_Syntax_Syntax.sigrng = uu____12131;
                                FStar_Syntax_Syntax.sigquals = qs;
                                FStar_Syntax_Syntax.sigmeta = uu____12133;
                                FStar_Syntax_Syntax.sigattrs = uu____12134;_},uu____12135),uu____12136)
                            ->
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.HasMaskedEffect qs))
                              &&
                              ((Prims.op_Negation is_rec) || (cfg.steps).zeta)
                        | uu____12201 -> true))
                      &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___89_12205  ->
                               match uu___89_12205 with
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
                          (let uu____12215 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____12215))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____12234) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____12269,uu____12270) -> false)))
                     in
                  let uu____12287 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____12303 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____12303 then (true, true) else (false, false)
                     in
                  match uu____12287 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____12316  ->
                            let uu____12317 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____12318 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____12319 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____12317 uu____12318 uu____12319);
                       if should_delta2
                       then
                         (let uu____12320 =
                            if fully
                            then
                              (((Cfg cfg) :: stack),
                                (let uu___151_12336 = cfg  in
                                 {
                                   steps =
                                     (let uu___152_12339 = cfg.steps  in
                                      {
                                        beta = (uu___152_12339.beta);
                                        iota = false;
                                        zeta = false;
                                        weak = false;
                                        hnf = false;
                                        primops = false;
                                        do_not_unfold_pure_lets =
                                          (uu___152_12339.do_not_unfold_pure_lets);
                                        unfold_until =
                                          (FStar_Pervasives_Native.Some
                                             FStar_Syntax_Syntax.Delta_constant);
                                        unfold_only =
                                          FStar_Pervasives_Native.None;
                                        unfold_fully =
                                          FStar_Pervasives_Native.None;
                                        unfold_attr =
                                          (uu___152_12339.unfold_attr);
                                        unfold_tac =
                                          (uu___152_12339.unfold_tac);
                                        pure_subterms_within_computations =
                                          (uu___152_12339.pure_subterms_within_computations);
                                        simplify = false;
                                        erase_universes =
                                          (uu___152_12339.erase_universes);
                                        allow_unbound_universes =
                                          (uu___152_12339.allow_unbound_universes);
                                        reify_ = (uu___152_12339.reify_);
                                        compress_uvars =
                                          (uu___152_12339.compress_uvars);
                                        no_full_norm =
                                          (uu___152_12339.no_full_norm);
                                        check_no_uvars =
                                          (uu___152_12339.check_no_uvars);
                                        unmeta = (uu___152_12339.unmeta);
                                        unascribe =
                                          (uu___152_12339.unascribe);
                                        in_full_norm_request =
                                          (uu___152_12339.in_full_norm_request);
                                        weakly_reduce_scrutinee =
                                          (uu___152_12339.weakly_reduce_scrutinee)
                                      });
                                   tcenv = (uu___151_12336.tcenv);
                                   debug = (uu___151_12336.debug);
                                   delta_level = (uu___151_12336.delta_level);
                                   primitive_steps =
                                     (uu___151_12336.primitive_steps);
                                   strong = (uu___151_12336.strong);
                                   memoize_lazy =
                                     (uu___151_12336.memoize_lazy);
                                   normalize_pure_lets =
                                     (uu___151_12336.normalize_pure_lets)
                                 }))
                            else (stack, cfg)  in
                          match uu____12320 with
                          | (stack1,cfg1) ->
                              do_unfold_fv cfg1 env stack1 t1 qninfo fv)
                       else rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____12353 = lookup_bvar env x  in
               (match uu____12353 with
                | Univ uu____12354 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____12403 = FStar_ST.op_Bang r  in
                      (match uu____12403 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____12525  ->
                                 let uu____12526 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____12527 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____12526
                                   uu____12527);
                            (let uu____12528 = maybe_weakly_reduced t'  in
                             if uu____12528
                             then
                               match stack with
                               | [] when
                                   (cfg.steps).weak ||
                                     (cfg.steps).compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____12529 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____12600)::uu____12601 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____12610)::uu____12611 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____12623,uu____12624))::stack_rest ->
                    (match c with
                     | Univ uu____12628 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____12637 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____12658  ->
                                    let uu____12659 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12659);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____12699  ->
                                    let uu____12700 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____12700);
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
                       (fun uu____12778  ->
                          let uu____12779 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____12779);
                     norm cfg env stack1 t1)
                | (Debug uu____12780)::uu____12781 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_12791 = cfg.steps  in
                             {
                               beta = (uu___153_12791.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12791.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12791.unfold_until);
                               unfold_only = (uu___153_12791.unfold_only);
                               unfold_fully = (uu___153_12791.unfold_fully);
                               unfold_attr = (uu___153_12791.unfold_attr);
                               unfold_tac = (uu___153_12791.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12791.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12791.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12791.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12791.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12791.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_12791.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_12793 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12793.tcenv);
                               debug = (uu___154_12793.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12793.primitive_steps);
                               strong = (uu___154_12793.strong);
                               memoize_lazy = (uu___154_12793.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12793.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12795 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12795 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12837  -> dummy :: env1) env)
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
                                          let uu____12874 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____12874)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_12879 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_12879.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_12879.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____12880 -> lopt  in
                           (log cfg
                              (fun uu____12886  ->
                                 let uu____12887 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____12887);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_12896 = cfg  in
                               {
                                 steps = (uu___156_12896.steps);
                                 tcenv = (uu___156_12896.tcenv);
                                 debug = (uu___156_12896.debug);
                                 delta_level = (uu___156_12896.delta_level);
                                 primitive_steps =
                                   (uu___156_12896.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_12896.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_12896.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____12907)::uu____12908 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_12920 = cfg.steps  in
                             {
                               beta = (uu___153_12920.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_12920.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_12920.unfold_until);
                               unfold_only = (uu___153_12920.unfold_only);
                               unfold_fully = (uu___153_12920.unfold_fully);
                               unfold_attr = (uu___153_12920.unfold_attr);
                               unfold_tac = (uu___153_12920.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_12920.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_12920.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_12920.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_12920.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_12920.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_12920.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_12922 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_12922.tcenv);
                               debug = (uu___154_12922.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_12922.primitive_steps);
                               strong = (uu___154_12922.strong);
                               memoize_lazy = (uu___154_12922.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_12922.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____12924 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____12924 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12966  -> dummy :: env1) env)
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
                                          let uu____13003 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13003)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_13008 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_13008.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_13008.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13009 -> lopt  in
                           (log cfg
                              (fun uu____13015  ->
                                 let uu____13016 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13016);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_13025 = cfg  in
                               {
                                 steps = (uu___156_13025.steps);
                                 tcenv = (uu___156_13025.tcenv);
                                 debug = (uu___156_13025.debug);
                                 delta_level = (uu___156_13025.delta_level);
                                 primitive_steps =
                                   (uu___156_13025.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_13025.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_13025.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____13036)::uu____13037 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_13051 = cfg.steps  in
                             {
                               beta = (uu___153_13051.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_13051.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_13051.unfold_until);
                               unfold_only = (uu___153_13051.unfold_only);
                               unfold_fully = (uu___153_13051.unfold_fully);
                               unfold_attr = (uu___153_13051.unfold_attr);
                               unfold_tac = (uu___153_13051.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_13051.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_13051.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_13051.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_13051.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_13051.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_13051.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_13053 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_13053.tcenv);
                               debug = (uu___154_13053.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_13053.primitive_steps);
                               strong = (uu___154_13053.strong);
                               memoize_lazy = (uu___154_13053.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_13053.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13055 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13055 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13097  -> dummy :: env1) env)
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
                                          let uu____13134 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13134)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_13139 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_13139.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_13139.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13140 -> lopt  in
                           (log cfg
                              (fun uu____13146  ->
                                 let uu____13147 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13147);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_13156 = cfg  in
                               {
                                 steps = (uu___156_13156.steps);
                                 tcenv = (uu___156_13156.tcenv);
                                 debug = (uu___156_13156.debug);
                                 delta_level = (uu___156_13156.delta_level);
                                 primitive_steps =
                                   (uu___156_13156.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_13156.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_13156.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____13167)::uu____13168 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_13182 = cfg.steps  in
                             {
                               beta = (uu___153_13182.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_13182.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_13182.unfold_until);
                               unfold_only = (uu___153_13182.unfold_only);
                               unfold_fully = (uu___153_13182.unfold_fully);
                               unfold_attr = (uu___153_13182.unfold_attr);
                               unfold_tac = (uu___153_13182.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_13182.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_13182.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_13182.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_13182.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_13182.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_13182.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_13184 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_13184.tcenv);
                               debug = (uu___154_13184.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_13184.primitive_steps);
                               strong = (uu___154_13184.strong);
                               memoize_lazy = (uu___154_13184.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_13184.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13186 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13186 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13228  -> dummy :: env1) env)
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
                                          let uu____13265 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13265)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_13270 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_13270.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_13270.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13271 -> lopt  in
                           (log cfg
                              (fun uu____13277  ->
                                 let uu____13278 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13278);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_13287 = cfg  in
                               {
                                 steps = (uu___156_13287.steps);
                                 tcenv = (uu___156_13287.tcenv);
                                 debug = (uu___156_13287.debug);
                                 delta_level = (uu___156_13287.delta_level);
                                 primitive_steps =
                                   (uu___156_13287.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_13287.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_13287.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____13298)::uu____13299 ->
                    if (cfg.steps).weak
                    then
                      let t2 =
                        if (cfg.steps).in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___153_13317 = cfg.steps  in
                             {
                               beta = (uu___153_13317.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_13317.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_13317.unfold_until);
                               unfold_only = (uu___153_13317.unfold_only);
                               unfold_fully = (uu___153_13317.unfold_fully);
                               unfold_attr = (uu___153_13317.unfold_attr);
                               unfold_tac = (uu___153_13317.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_13317.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_13317.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_13317.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_13317.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_13317.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_13317.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_13319 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_13319.tcenv);
                               debug = (uu___154_13319.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_13319.primitive_steps);
                               strong = (uu___154_13319.strong);
                               memoize_lazy = (uu___154_13319.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_13319.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13321 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13321 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13363  -> dummy :: env1) env)
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
                                          let uu____13400 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13400)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_13405 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_13405.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_13405.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13406 -> lopt  in
                           (log cfg
                              (fun uu____13412  ->
                                 let uu____13413 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13413);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_13422 = cfg  in
                               {
                                 steps = (uu___156_13422.steps);
                                 tcenv = (uu___156_13422.tcenv);
                                 debug = (uu___156_13422.debug);
                                 delta_level = (uu___156_13422.delta_level);
                                 primitive_steps =
                                   (uu___156_13422.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_13422.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_13422.normalize_pure_lets)
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
                             let uu___153_13436 = cfg.steps  in
                             {
                               beta = (uu___153_13436.beta);
                               iota = false;
                               zeta = false;
                               weak = false;
                               hnf = (uu___153_13436.hnf);
                               primops = false;
                               do_not_unfold_pure_lets = true;
                               unfold_until = (uu___153_13436.unfold_until);
                               unfold_only = (uu___153_13436.unfold_only);
                               unfold_fully = (uu___153_13436.unfold_fully);
                               unfold_attr = (uu___153_13436.unfold_attr);
                               unfold_tac = (uu___153_13436.unfold_tac);
                               pure_subterms_within_computations = false;
                               simplify = false;
                               erase_universes =
                                 (uu___153_13436.erase_universes);
                               allow_unbound_universes =
                                 (uu___153_13436.allow_unbound_universes);
                               reify_ = false;
                               compress_uvars =
                                 (uu___153_13436.compress_uvars);
                               no_full_norm = true;
                               check_no_uvars =
                                 (uu___153_13436.check_no_uvars);
                               unmeta = false;
                               unascribe = false;
                               in_full_norm_request =
                                 (uu___153_13436.in_full_norm_request);
                               weakly_reduce_scrutinee =
                                 (uu___153_13436.weakly_reduce_scrutinee)
                             }  in
                           let cfg' =
                             let uu___154_13438 = cfg  in
                             {
                               steps = steps';
                               tcenv = (uu___154_13438.tcenv);
                               debug = (uu___154_13438.debug);
                               delta_level = [FStar_TypeChecker_Env.NoDelta];
                               primitive_steps =
                                 (uu___154_13438.primitive_steps);
                               strong = (uu___154_13438.strong);
                               memoize_lazy = (uu___154_13438.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___154_13438.normalize_pure_lets)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____13440 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____13440 with
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
                                          let uu____13519 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____13519)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___155_13524 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___155_13524.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___155_13524.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____13525 -> lopt  in
                           (log cfg
                              (fun uu____13531  ->
                                 let uu____13532 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____13532);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___156_13541 = cfg  in
                               {
                                 steps = (uu___156_13541.steps);
                                 tcenv = (uu___156_13541.tcenv);
                                 debug = (uu___156_13541.debug);
                                 delta_level = (uu___156_13541.delta_level);
                                 primitive_steps =
                                   (uu___156_13541.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___156_13541.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___156_13541.normalize_pure_lets)
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
                      (fun uu____13590  ->
                         fun stack1  ->
                           match uu____13590 with
                           | (a,aq) ->
                               let uu____13602 =
                                 let uu____13603 =
                                   let uu____13610 =
                                     let uu____13611 =
                                       let uu____13642 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____13642, false)  in
                                     Clos uu____13611  in
                                   (uu____13610, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____13603  in
                               uu____13602 :: stack1) args)
                  in
               (log cfg
                  (fun uu____13726  ->
                     let uu____13727 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____13727);
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
                             ((let uu___157_13763 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___157_13763.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___157_13763.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____13764 ->
                      let uu____13769 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____13769)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____13772 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____13772 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____13803 =
                          let uu____13804 =
                            let uu____13811 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___158_13813 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___158_13813.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___158_13813.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____13811)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____13804  in
                        mk uu____13803 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____13832 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____13832
               else
                 (let uu____13834 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____13834 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____13842 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____13866  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____13842 c1  in
                      let t2 =
                        let uu____13888 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____13888 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____13999)::uu____14000 ->
                    (log cfg
                       (fun uu____14013  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____14014)::uu____14015 ->
                    (log cfg
                       (fun uu____14026  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____14027,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____14028;
                                   FStar_Syntax_Syntax.vars = uu____14029;_},uu____14030,uu____14031))::uu____14032
                    ->
                    (log cfg
                       (fun uu____14041  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____14042)::uu____14043 ->
                    (log cfg
                       (fun uu____14054  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____14055 ->
                    (log cfg
                       (fun uu____14058  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____14062  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____14079 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____14079
                         | FStar_Util.Inr c ->
                             let uu____14087 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____14087
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____14100 =
                               let uu____14101 =
                                 let uu____14128 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14128, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14101
                                in
                             mk uu____14100 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____14147 ->
                           let uu____14148 =
                             let uu____14149 =
                               let uu____14150 =
                                 let uu____14177 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____14177, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____14150
                                in
                             mk uu____14149 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____14148))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 if
                   ((cfg.steps).iota && (cfg.steps).weakly_reduce_scrutinee)
                     && (Prims.op_Negation (cfg.steps).weak)
                 then
                   let uu___159_14254 = cfg  in
                   {
                     steps =
                       (let uu___160_14257 = cfg.steps  in
                        {
                          beta = (uu___160_14257.beta);
                          iota = (uu___160_14257.iota);
                          zeta = (uu___160_14257.zeta);
                          weak = true;
                          hnf = (uu___160_14257.hnf);
                          primops = (uu___160_14257.primops);
                          do_not_unfold_pure_lets =
                            (uu___160_14257.do_not_unfold_pure_lets);
                          unfold_until = (uu___160_14257.unfold_until);
                          unfold_only = (uu___160_14257.unfold_only);
                          unfold_fully = (uu___160_14257.unfold_fully);
                          unfold_attr = (uu___160_14257.unfold_attr);
                          unfold_tac = (uu___160_14257.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___160_14257.pure_subterms_within_computations);
                          simplify = (uu___160_14257.simplify);
                          erase_universes = (uu___160_14257.erase_universes);
                          allow_unbound_universes =
                            (uu___160_14257.allow_unbound_universes);
                          reify_ = (uu___160_14257.reify_);
                          compress_uvars = (uu___160_14257.compress_uvars);
                          no_full_norm = (uu___160_14257.no_full_norm);
                          check_no_uvars = (uu___160_14257.check_no_uvars);
                          unmeta = (uu___160_14257.unmeta);
                          unascribe = (uu___160_14257.unascribe);
                          in_full_norm_request =
                            (uu___160_14257.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___160_14257.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___159_14254.tcenv);
                     debug = (uu___159_14254.debug);
                     delta_level = (uu___159_14254.delta_level);
                     primitive_steps = (uu___159_14254.primitive_steps);
                     strong = (uu___159_14254.strong);
                     memoize_lazy = (uu___159_14254.memoize_lazy);
                     normalize_pure_lets =
                       (uu___159_14254.normalize_pure_lets)
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
                         let uu____14293 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____14293 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___161_14313 = cfg  in
                               let uu____14314 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___161_14313.steps);
                                 tcenv = uu____14314;
                                 debug = (uu___161_14313.debug);
                                 delta_level = (uu___161_14313.delta_level);
                                 primitive_steps =
                                   (uu___161_14313.primitive_steps);
                                 strong = (uu___161_14313.strong);
                                 memoize_lazy = (uu___161_14313.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___161_14313.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____14321 =
                                 let uu____14322 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____14322  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____14321
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___162_14325 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___162_14325.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___162_14325.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___162_14325.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___162_14325.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____14326 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14326
           | FStar_Syntax_Syntax.Tm_let
               ((uu____14337,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____14338;
                               FStar_Syntax_Syntax.lbunivs = uu____14339;
                               FStar_Syntax_Syntax.lbtyp = uu____14340;
                               FStar_Syntax_Syntax.lbeff = uu____14341;
                               FStar_Syntax_Syntax.lbdef = uu____14342;
                               FStar_Syntax_Syntax.lbattrs = uu____14343;
                               FStar_Syntax_Syntax.lbpos = uu____14344;_}::uu____14345),uu____14346)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____14386 =
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
               if uu____14386
               then
                 let binder =
                   let uu____14388 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____14388  in
                 let env1 =
                   let uu____14398 =
                     let uu____14405 =
                       let uu____14406 =
                         let uu____14437 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____14437,
                           false)
                          in
                       Clos uu____14406  in
                     ((FStar_Pervasives_Native.Some binder), uu____14405)  in
                   uu____14398 :: env  in
                 (log cfg
                    (fun uu____14530  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____14534  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____14535 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____14535))
                 else
                   (let uu____14537 =
                      let uu____14542 =
                        let uu____14543 =
                          let uu____14544 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____14544
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____14543]  in
                      FStar_Syntax_Subst.open_term uu____14542 body  in
                    match uu____14537 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____14553  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____14561 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____14561  in
                            FStar_Util.Inl
                              (let uu___163_14571 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___163_14571.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___163_14571.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____14574  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___164_14576 = lb  in
                             let uu____14577 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___164_14576.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___164_14576.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____14577;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___164_14576.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___164_14576.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14612  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___165_14635 = cfg  in
                             {
                               steps = (uu___165_14635.steps);
                               tcenv = (uu___165_14635.tcenv);
                               debug = (uu___165_14635.debug);
                               delta_level = (uu___165_14635.delta_level);
                               primitive_steps =
                                 (uu___165_14635.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___165_14635.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___165_14635.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____14638  ->
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
               let uu____14655 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____14655 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____14691 =
                               let uu___166_14692 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___166_14692.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___166_14692.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____14691  in
                           let uu____14693 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____14693 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____14719 =
                                   FStar_List.map (fun uu____14735  -> dummy)
                                     lbs1
                                    in
                                 let uu____14736 =
                                   let uu____14745 =
                                     FStar_List.map
                                       (fun uu____14765  -> dummy) xs1
                                      in
                                   FStar_List.append uu____14745 env  in
                                 FStar_List.append uu____14719 uu____14736
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____14789 =
                                       let uu___167_14790 = rc  in
                                       let uu____14791 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___167_14790.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____14791;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___167_14790.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____14789
                                 | uu____14798 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___168_14802 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___168_14802.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___168_14802.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___168_14802.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___168_14802.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____14812 =
                        FStar_List.map (fun uu____14828  -> dummy) lbs2  in
                      FStar_List.append uu____14812 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____14836 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____14836 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___169_14852 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___169_14852.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___169_14852.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____14879 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____14879
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____14898 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____14974  ->
                        match uu____14974 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___170_15095 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___170_15095.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___170_15095.FStar_Syntax_Syntax.sort)
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
                              (i + (Prims.lift_native_int (1)))))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], (Prims.lift_native_int (0)))
                  in
               (match uu____14898 with
                | (rec_env,memos,uu____15308) ->
                    let uu____15361 =
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
                             let uu____15684 =
                               let uu____15691 =
                                 let uu____15692 =
                                   let uu____15723 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____15723, false)
                                    in
                                 Clos uu____15692  in
                               (FStar_Pervasives_Native.None, uu____15691)
                                in
                             uu____15684 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____15833  ->
                     let uu____15834 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____15834);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____15856 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____15858::uu____15859 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____15864) ->
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
                             | uu____15887 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____15901 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____15901
                              | uu____15912 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____15916 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____15942 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____15960 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____15977 =
                        let uu____15978 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____15979 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____15978 uu____15979
                         in
                      failwith uu____15977
                    else rebuild cfg env stack t2
                | uu____15981 -> norm cfg env stack t2))

and do_unfold_fv :
  cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Env.qninfo ->
            FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t0  ->
          fun qninfo  ->
            fun f  ->
              let r_env =
                let uu____15991 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____15991  in
              let uu____15992 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____15992 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____16005  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____16016  ->
                        let uu____16017 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____16018 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____16017 uu____16018);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____16023 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____16023 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.lift_native_int (0))
                    then
                      match stack with
                      | (UnivArgs (us',uu____16032))::stack1 ->
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
                      | uu____16087 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____16090 ->
                          let uu____16093 =
                            let uu____16094 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____16094
                             in
                          failwith uu____16093
                    else norm cfg env stack t1))

and reduce_impure_comp :
  cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,(FStar_Syntax_Syntax.monad_name,
                                            FStar_Syntax_Syntax.monad_name)
                                            FStar_Pervasives_Native.tuple2)
            FStar_Util.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
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
                  let uu___171_16118 = cfg  in
                  let uu____16119 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____16119;
                    tcenv = (uu___171_16118.tcenv);
                    debug = (uu___171_16118.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___171_16118.primitive_steps);
                    strong = (uu___171_16118.strong);
                    memoize_lazy = (uu___171_16118.memoize_lazy);
                    normalize_pure_lets =
                      (uu___171_16118.normalize_pure_lets)
                  }
                else
                  (let uu___172_16121 = cfg  in
                   {
                     steps =
                       (let uu___173_16124 = cfg.steps  in
                        {
                          beta = (uu___173_16124.beta);
                          iota = (uu___173_16124.iota);
                          zeta = false;
                          weak = (uu___173_16124.weak);
                          hnf = (uu___173_16124.hnf);
                          primops = (uu___173_16124.primops);
                          do_not_unfold_pure_lets =
                            (uu___173_16124.do_not_unfold_pure_lets);
                          unfold_until = (uu___173_16124.unfold_until);
                          unfold_only = (uu___173_16124.unfold_only);
                          unfold_fully = (uu___173_16124.unfold_fully);
                          unfold_attr = (uu___173_16124.unfold_attr);
                          unfold_tac = (uu___173_16124.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___173_16124.pure_subterms_within_computations);
                          simplify = (uu___173_16124.simplify);
                          erase_universes = (uu___173_16124.erase_universes);
                          allow_unbound_universes =
                            (uu___173_16124.allow_unbound_universes);
                          reify_ = (uu___173_16124.reify_);
                          compress_uvars = (uu___173_16124.compress_uvars);
                          no_full_norm = (uu___173_16124.no_full_norm);
                          check_no_uvars = (uu___173_16124.check_no_uvars);
                          unmeta = (uu___173_16124.unmeta);
                          unascribe = (uu___173_16124.unascribe);
                          in_full_norm_request =
                            (uu___173_16124.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___173_16124.weakly_reduce_scrutinee)
                        });
                     tcenv = (uu___172_16121.tcenv);
                     debug = (uu___172_16121.debug);
                     delta_level = (uu___172_16121.delta_level);
                     primitive_steps = (uu___172_16121.primitive_steps);
                     strong = (uu___172_16121.strong);
                     memoize_lazy = (uu___172_16121.memoize_lazy);
                     normalize_pure_lets =
                       (uu___172_16121.normalize_pure_lets)
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

and do_reify_monadic :
  (unit -> FStar_Syntax_Syntax.term) ->
    cfg ->
      env ->
        stack_elt Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.monad_name ->
              FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
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
                  (fun uu____16154  ->
                     let uu____16155 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____16156 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____16155
                       uu____16156);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____16158 =
                   let uu____16159 = FStar_Syntax_Subst.compress head3  in
                   uu____16159.FStar_Syntax_Syntax.n  in
                 match uu____16158 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____16177 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16177
                        in
                     let uu____16178 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16178 with
                      | (uu____16179,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____16185 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____16195 =
                                   let uu____16196 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____16196.FStar_Syntax_Syntax.n  in
                                 match uu____16195 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____16202,uu____16203))
                                     ->
                                     let uu____16212 =
                                       let uu____16213 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____16213.FStar_Syntax_Syntax.n  in
                                     (match uu____16212 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____16219,msrc,uu____16221))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____16230 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16230
                                      | uu____16231 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____16232 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____16233 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____16233 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___174_16238 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___174_16238.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___174_16238.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___174_16238.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___174_16238.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___174_16238.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____16239 = FStar_List.tl stack  in
                                    let uu____16240 =
                                      let uu____16241 =
                                        let uu____16248 =
                                          let uu____16249 =
                                            let uu____16262 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____16262)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____16249
                                           in
                                        FStar_Syntax_Syntax.mk uu____16248
                                         in
                                      uu____16241
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____16239 uu____16240
                                | FStar_Pervasives_Native.None  ->
                                    let uu____16278 =
                                      let uu____16279 = is_return body  in
                                      match uu____16279 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____16283;
                                            FStar_Syntax_Syntax.vars =
                                              uu____16284;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____16289 -> false  in
                                    if uu____16278
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
                                         let uu____16312 =
                                           let uu____16319 =
                                             let uu____16320 =
                                               let uu____16337 =
                                                 let uu____16340 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____16340]  in
                                               (uu____16337, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____16320
                                              in
                                           FStar_Syntax_Syntax.mk uu____16319
                                            in
                                         uu____16312
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____16358 =
                                           let uu____16359 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____16359.FStar_Syntax_Syntax.n
                                            in
                                         match uu____16358 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____16365::uu____16366::[])
                                             ->
                                             let uu____16373 =
                                               let uu____16380 =
                                                 let uu____16381 =
                                                   let uu____16388 =
                                                     let uu____16391 =
                                                       let uu____16392 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____16392
                                                        in
                                                     let uu____16393 =
                                                       let uu____16396 =
                                                         let uu____16397 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____16397
                                                          in
                                                       [uu____16396]  in
                                                     uu____16391 ::
                                                       uu____16393
                                                      in
                                                   (bind1, uu____16388)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____16381
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____16380
                                                in
                                             uu____16373
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____16405 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____16411 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____16411
                                         then
                                           let uu____16414 =
                                             let uu____16415 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16415
                                              in
                                           let uu____16416 =
                                             let uu____16419 =
                                               let uu____16420 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____16420
                                                in
                                             [uu____16419]  in
                                           uu____16414 :: uu____16416
                                         else []  in
                                       let reified =
                                         let uu____16425 =
                                           let uu____16432 =
                                             let uu____16433 =
                                               let uu____16448 =
                                                 let uu____16451 =
                                                   let uu____16454 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____16455 =
                                                     let uu____16458 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____16458]  in
                                                   uu____16454 :: uu____16455
                                                    in
                                                 let uu____16459 =
                                                   let uu____16462 =
                                                     let uu____16465 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____16466 =
                                                       let uu____16469 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____16470 =
                                                         let uu____16473 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____16474 =
                                                           let uu____16477 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____16477]  in
                                                         uu____16473 ::
                                                           uu____16474
                                                          in
                                                       uu____16469 ::
                                                         uu____16470
                                                        in
                                                     uu____16465 ::
                                                       uu____16466
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____16462
                                                    in
                                                 FStar_List.append
                                                   uu____16451 uu____16459
                                                  in
                                               (bind_inst, uu____16448)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____16433
                                              in
                                           FStar_Syntax_Syntax.mk uu____16432
                                            in
                                         uu____16425
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____16489  ->
                                            let uu____16490 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____16491 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____16490 uu____16491);
                                       (let uu____16492 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____16492 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____16516 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____16516
                        in
                     let uu____16517 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____16517 with
                      | (uu____16518,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____16557 =
                                  let uu____16558 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____16558.FStar_Syntax_Syntax.n  in
                                match uu____16557 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____16564) -> t2
                                | uu____16569 -> head4  in
                              let uu____16570 =
                                let uu____16571 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____16571.FStar_Syntax_Syntax.n  in
                              match uu____16570 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____16577 -> FStar_Pervasives_Native.None
                               in
                            let uu____16578 = maybe_extract_fv head4  in
                            match uu____16578 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____16588 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____16588
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____16593 = maybe_extract_fv head5
                                     in
                                  match uu____16593 with
                                  | FStar_Pervasives_Native.Some uu____16598
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____16599 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____16604 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____16621 =
                              match uu____16621 with
                              | (e,q) ->
                                  let uu____16628 =
                                    let uu____16629 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____16629.FStar_Syntax_Syntax.n  in
                                  (match uu____16628 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____16644 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____16644
                                   | uu____16645 -> false)
                               in
                            let uu____16646 =
                              let uu____16647 =
                                let uu____16654 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____16654 :: args  in
                              FStar_Util.for_some is_arg_impure uu____16647
                               in
                            if uu____16646
                            then
                              let uu____16659 =
                                let uu____16660 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____16660
                                 in
                              failwith uu____16659
                            else ());
                           (let uu____16662 = maybe_unfold_action head_app
                               in
                            match uu____16662 with
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
                                   (fun uu____16705  ->
                                      let uu____16706 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____16707 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____16706 uu____16707);
                                 (let uu____16708 = FStar_List.tl stack  in
                                  norm cfg env uu____16708 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____16710) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____16734 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____16734  in
                     (log cfg
                        (fun uu____16738  ->
                           let uu____16739 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____16739);
                      (let uu____16740 = FStar_List.tl stack  in
                       norm cfg env uu____16740 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____16861  ->
                               match uu____16861 with
                               | (pat,wopt,tm) ->
                                   let uu____16909 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____16909)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____16941 = FStar_List.tl stack  in
                     norm cfg env uu____16941 tm
                 | uu____16942 -> fallback ())

and reify_lift :
  cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            let env = cfg.tcenv  in
            log cfg
              (fun uu____16956  ->
                 let uu____16957 = FStar_Ident.string_of_lid msrc  in
                 let uu____16958 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16959 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16957
                   uu____16958 uu____16959);
            (let uu____16960 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____16960
             then
               let ed =
                 let uu____16962 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____16962  in
               let uu____16963 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____16963 with
               | (uu____16964,return_repr) ->
                   let return_inst =
                     let uu____16973 =
                       let uu____16974 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____16974.FStar_Syntax_Syntax.n  in
                     match uu____16973 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____16980::[]) ->
                         let uu____16987 =
                           let uu____16994 =
                             let uu____16995 =
                               let uu____17002 =
                                 let uu____17005 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17005]  in
                               (return_tm, uu____17002)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____16995  in
                           FStar_Syntax_Syntax.mk uu____16994  in
                         uu____16987 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17013 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17016 =
                     let uu____17023 =
                       let uu____17024 =
                         let uu____17039 =
                           let uu____17042 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17043 =
                             let uu____17046 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17046]  in
                           uu____17042 :: uu____17043  in
                         (return_inst, uu____17039)  in
                       FStar_Syntax_Syntax.Tm_app uu____17024  in
                     FStar_Syntax_Syntax.mk uu____17023  in
                   uu____17016 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17055 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17055 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17058 =
                      let uu____17059 = FStar_Ident.text_of_lid msrc  in
                      let uu____17060 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17059 uu____17060
                       in
                    failwith uu____17058
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17061;
                      FStar_TypeChecker_Env.mtarget = uu____17062;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17063;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17085 =
                      let uu____17086 = FStar_Ident.text_of_lid msrc  in
                      let uu____17087 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17086 uu____17087
                       in
                    failwith uu____17085
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17088;
                      FStar_TypeChecker_Env.mtarget = uu____17089;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17090;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____17125 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____17126 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____17125 t FStar_Syntax_Syntax.tun uu____17126))

and norm_pattern_args :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____17182  ->
                   match uu____17182 with
                   | (a,imp) ->
                       let uu____17193 = norm cfg env [] a  in
                       (uu____17193, imp))))

and norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____17201  ->
             let uu____17202 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17203 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____17202 uu____17203);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17227 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____17227
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___175_17230 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___175_17230.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___175_17230.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17250 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____17250
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___176_17253 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___176_17253.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___176_17253.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17288  ->
                      match uu____17288 with
                      | (a,i) ->
                          let uu____17299 = norm cfg env [] a  in
                          (uu____17299, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___90_17317  ->
                       match uu___90_17317 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17321 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17321
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___177_17329 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___178_17332 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___178_17332.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___177_17329.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___177_17329.FStar_Syntax_Syntax.vars)
             })

and norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder =
  fun cfg  ->
    fun env  ->
      fun uu____17335  ->
        match uu____17335 with
        | (x,imp) ->
            let uu____17338 =
              let uu___179_17339 = x  in
              let uu____17340 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___179_17339.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___179_17339.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17340
              }  in
            (uu____17338, imp)

and norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17346 =
          FStar_List.fold_left
            (fun uu____17364  ->
               fun b  ->
                 match uu____17364 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17346 with | (nbs,uu____17404) -> FStar_List.rev nbs

and norm_lcomp_opt :
  cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags1 =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags
               in
            let uu____17420 =
              let uu___180_17421 = rc  in
              let uu____17422 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___180_17421.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17422;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___180_17421.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17420
        | uu____17429 -> lopt

and maybe_simplify :
  cfg ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
      closure) FStar_Pervasives_Native.tuple2 Prims.list ->
      stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.debug).b380
          then
            (let uu____17450 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17451 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____17450
               uu____17451)
          else ();
          tm'

and maybe_simplify_aux :
  cfg ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
      closure) FStar_Pervasives_Native.tuple2 Prims.list ->
      stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____17471 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____17471
          then tm1
          else
            (let w t =
               let uu___181_17485 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___181_17485.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___181_17485.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17496 =
                 let uu____17497 = FStar_Syntax_Util.unmeta t  in
                 uu____17497.FStar_Syntax_Syntax.n  in
               match uu____17496 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17504 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17553)::args1,(bv,uu____17556)::bs1) ->
                   let uu____17590 =
                     let uu____17591 = FStar_Syntax_Subst.compress t  in
                     uu____17591.FStar_Syntax_Syntax.n  in
                   (match uu____17590 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17595 -> false)
               | ([],[]) -> true
               | (uu____17616,uu____17617) -> false  in
             let is_applied bs t =
               let uu____17657 = FStar_Syntax_Util.head_and_args' t  in
               match uu____17657 with
               | (hd1,args) ->
                   let uu____17690 =
                     let uu____17691 = FStar_Syntax_Subst.compress hd1  in
                     uu____17691.FStar_Syntax_Syntax.n  in
                   (match uu____17690 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____17697 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____17713 = FStar_Syntax_Util.is_squash t  in
               match uu____17713 with
               | FStar_Pervasives_Native.Some (uu____17724,t') ->
                   is_applied bs t'
               | uu____17736 ->
                   let uu____17745 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____17745 with
                    | FStar_Pervasives_Native.Some (uu____17756,t') ->
                        is_applied bs t'
                    | uu____17768 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____17787 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17787 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____17794)::(q,uu____17796)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____17831 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____17831 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____17836 =
                          let uu____17837 = FStar_Syntax_Subst.compress p  in
                          uu____17837.FStar_Syntax_Syntax.n  in
                        (match uu____17836 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____17843 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____17843
                         | uu____17844 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____17847)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____17872 =
                          let uu____17873 = FStar_Syntax_Subst.compress p1
                             in
                          uu____17873.FStar_Syntax_Syntax.n  in
                        (match uu____17872 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____17879 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____17879
                         | uu____17880 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____17884 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____17884 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____17889 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____17889 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____17896 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____17896
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____17899)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____17924 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____17924 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____17931 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____17931
                              | uu____17932 -> FStar_Pervasives_Native.None)
                         | uu____17935 -> FStar_Pervasives_Native.None)
                    | uu____17938 -> FStar_Pervasives_Native.None)
               | uu____17941 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____17954 =
                 let uu____17955 = FStar_Syntax_Subst.compress phi  in
                 uu____17955.FStar_Syntax_Syntax.n  in
               match uu____17954 with
               | FStar_Syntax_Syntax.Tm_match (uu____17960,br::brs) ->
                   let uu____18027 = br  in
                   (match uu____18027 with
                    | (uu____18044,uu____18045,e) ->
                        let r =
                          let uu____18066 = simp_t e  in
                          match uu____18066 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18072 =
                                FStar_List.for_all
                                  (fun uu____18090  ->
                                     match uu____18090 with
                                     | (uu____18103,uu____18104,e') ->
                                         let uu____18118 = simp_t e'  in
                                         uu____18118 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18072
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18126 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18133 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18133
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18158 =
                 match uu____18158 with
                 | (t1,q) ->
                     let uu____18171 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18171 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18199 -> (t1, q))
                  in
               let uu____18208 = FStar_Syntax_Util.head_and_args t  in
               match uu____18208 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18272 =
                 let uu____18273 = FStar_Syntax_Util.unmeta ty  in
                 uu____18273.FStar_Syntax_Syntax.n  in
               match uu____18272 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18277) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18282,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18302 -> false  in
             let simplify1 arg =
               let uu____18327 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18327, arg)  in
             let uu____18336 = is_quantified_const tm1  in
             match uu____18336 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____18340 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____18340
             | FStar_Pervasives_Native.None  ->
                 let uu____18341 =
                   let uu____18342 = FStar_Syntax_Subst.compress tm1  in
                   uu____18342.FStar_Syntax_Syntax.n  in
                 (match uu____18341 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18346;
                              FStar_Syntax_Syntax.vars = uu____18347;_},uu____18348);
                         FStar_Syntax_Syntax.pos = uu____18349;
                         FStar_Syntax_Syntax.vars = uu____18350;_},args)
                      ->
                      let uu____18376 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18376
                      then
                        let uu____18377 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18377 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18424)::
                             (uu____18425,(arg,uu____18427))::[] ->
                             maybe_auto_squash arg
                         | (uu____18476,(arg,uu____18478))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18479)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18528)::uu____18529::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18580::(FStar_Pervasives_Native.Some (false
                                         ),uu____18581)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18632 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18646 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18646
                         then
                           let uu____18647 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18647 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18694)::uu____18695::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18746::(FStar_Pervasives_Native.Some (true
                                           ),uu____18747)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18798)::(uu____18799,(arg,uu____18801))::[]
                               -> maybe_auto_squash arg
                           | (uu____18850,(arg,uu____18852))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18853)::[]
                               -> maybe_auto_squash arg
                           | uu____18902 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18916 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18916
                            then
                              let uu____18917 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18917 with
                              | uu____18964::(FStar_Pervasives_Native.Some
                                              (true ),uu____18965)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19016)::uu____19017::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19068)::(uu____19069,(arg,uu____19071))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19120,(p,uu____19122))::(uu____19123,
                                                                (q,uu____19125))::[]
                                  ->
                                  let uu____19172 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19172
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19174 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19188 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19188
                               then
                                 let uu____19189 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19189 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19236)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19237)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19288)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19289)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19340)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19341)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19392)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19393)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19444,(arg,uu____19446))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19447)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19496)::(uu____19497,(arg,uu____19499))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19548,(arg,uu____19550))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19551)::[]
                                     ->
                                     let uu____19600 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19600
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19601)::(uu____19602,(arg,uu____19604))::[]
                                     ->
                                     let uu____19653 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19653
                                 | (uu____19654,(p,uu____19656))::(uu____19657,
                                                                   (q,uu____19659))::[]
                                     ->
                                     let uu____19706 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19706
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19708 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19722 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19722
                                  then
                                    let uu____19723 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19723 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19770)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19801)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19832 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19846 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19846
                                     then
                                       match args with
                                       | (t,uu____19848)::[] ->
                                           let uu____19865 =
                                             let uu____19866 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19866.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19865 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19869::[],body,uu____19871)
                                                ->
                                                let uu____19898 = simp_t body
                                                   in
                                                (match uu____19898 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19901 -> tm1)
                                            | uu____19904 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19906))::(t,uu____19908)::[]
                                           ->
                                           let uu____19947 =
                                             let uu____19948 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19948.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19947 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19951::[],body,uu____19953)
                                                ->
                                                let uu____19980 = simp_t body
                                                   in
                                                (match uu____19980 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19983 -> tm1)
                                            | uu____19986 -> tm1)
                                       | uu____19987 -> tm1
                                     else
                                       (let uu____19997 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____19997
                                        then
                                          match args with
                                          | (t,uu____19999)::[] ->
                                              let uu____20016 =
                                                let uu____20017 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20017.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20016 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20020::[],body,uu____20022)
                                                   ->
                                                   let uu____20049 =
                                                     simp_t body  in
                                                   (match uu____20049 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20052 -> tm1)
                                               | uu____20055 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20057))::(t,uu____20059)::[]
                                              ->
                                              let uu____20098 =
                                                let uu____20099 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20099.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20098 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20102::[],body,uu____20104)
                                                   ->
                                                   let uu____20131 =
                                                     simp_t body  in
                                                   (match uu____20131 with
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
                                                    | uu____20134 -> tm1)
                                               | uu____20137 -> tm1)
                                          | uu____20138 -> tm1
                                        else
                                          (let uu____20148 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20148
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20149;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20150;_},uu____20151)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20168;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20169;_},uu____20170)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20187 -> tm1
                                           else
                                             (let uu____20197 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20197 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20217 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20227;
                         FStar_Syntax_Syntax.vars = uu____20228;_},args)
                      ->
                      let uu____20250 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20250
                      then
                        let uu____20251 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20251 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20298)::
                             (uu____20299,(arg,uu____20301))::[] ->
                             maybe_auto_squash arg
                         | (uu____20350,(arg,uu____20352))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20353)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20402)::uu____20403::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20454::(FStar_Pervasives_Native.Some (false
                                         ),uu____20455)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20506 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20520 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20520
                         then
                           let uu____20521 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20521 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____20568)::uu____20569::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____20620::(FStar_Pervasives_Native.Some (true
                                           ),uu____20621)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____20672)::(uu____20673,(arg,uu____20675))::[]
                               -> maybe_auto_squash arg
                           | (uu____20724,(arg,uu____20726))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____20727)::[]
                               -> maybe_auto_squash arg
                           | uu____20776 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____20790 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____20790
                            then
                              let uu____20791 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____20791 with
                              | uu____20838::(FStar_Pervasives_Native.Some
                                              (true ),uu____20839)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____20890)::uu____20891::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____20942)::(uu____20943,(arg,uu____20945))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20994,(p,uu____20996))::(uu____20997,
                                                                (q,uu____20999))::[]
                                  ->
                                  let uu____21046 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21046
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21048 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21062 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21062
                               then
                                 let uu____21063 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21063 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21110)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21111)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21162)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21163)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21214)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21215)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21266)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21267)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21318,(arg,uu____21320))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21321)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21370)::(uu____21371,(arg,uu____21373))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21422,(arg,uu____21424))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21425)::[]
                                     ->
                                     let uu____21474 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21474
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21475)::(uu____21476,(arg,uu____21478))::[]
                                     ->
                                     let uu____21527 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21527
                                 | (uu____21528,(p,uu____21530))::(uu____21531,
                                                                   (q,uu____21533))::[]
                                     ->
                                     let uu____21580 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21580
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21582 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21596 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____21596
                                  then
                                    let uu____21597 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____21597 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____21644)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21675)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21706 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21720 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21720
                                     then
                                       match args with
                                       | (t,uu____21722)::[] ->
                                           let uu____21739 =
                                             let uu____21740 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21740.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21739 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21743::[],body,uu____21745)
                                                ->
                                                let uu____21772 = simp_t body
                                                   in
                                                (match uu____21772 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21775 -> tm1)
                                            | uu____21778 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21780))::(t,uu____21782)::[]
                                           ->
                                           let uu____21821 =
                                             let uu____21822 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21822.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21821 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21825::[],body,uu____21827)
                                                ->
                                                let uu____21854 = simp_t body
                                                   in
                                                (match uu____21854 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21857 -> tm1)
                                            | uu____21860 -> tm1)
                                       | uu____21861 -> tm1
                                     else
                                       (let uu____21871 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21871
                                        then
                                          match args with
                                          | (t,uu____21873)::[] ->
                                              let uu____21890 =
                                                let uu____21891 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21891.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21890 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21894::[],body,uu____21896)
                                                   ->
                                                   let uu____21923 =
                                                     simp_t body  in
                                                   (match uu____21923 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21926 -> tm1)
                                               | uu____21929 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21931))::(t,uu____21933)::[]
                                              ->
                                              let uu____21972 =
                                                let uu____21973 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21973.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21972 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21976::[],body,uu____21978)
                                                   ->
                                                   let uu____22005 =
                                                     simp_t body  in
                                                   (match uu____22005 with
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
                                                    | uu____22008 -> tm1)
                                               | uu____22011 -> tm1)
                                          | uu____22012 -> tm1
                                        else
                                          (let uu____22022 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22022
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22023;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22024;_},uu____22025)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22042;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22043;_},uu____22044)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22061 -> tm1
                                           else
                                             (let uu____22071 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____22071 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____22091 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____22106 = simp_t t  in
                      (match uu____22106 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22109 ->
                      let uu____22132 = is_const_match tm1  in
                      (match uu____22132 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____22135 -> tm1))

and rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____22145  ->
               (let uu____22147 = FStar_Syntax_Print.tag_of_term t  in
                let uu____22148 = FStar_Syntax_Print.term_to_string t  in
                let uu____22149 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____22156 =
                  let uu____22157 =
                    let uu____22160 =
                      firstn (Prims.lift_native_int (4)) stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____22160
                     in
                  stack_to_string uu____22157  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____22147 uu____22148 uu____22149 uu____22156);
               (let uu____22183 =
                  FStar_TypeChecker_Env.debug cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____22183
                then
                  let uu____22184 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____22184 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____22191 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____22192 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____22193 =
                          let uu____22194 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____22194
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____22191
                          uu____22192 uu____22193);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____22212 =
                     let uu____22213 =
                       let uu____22214 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____22214  in
                     FStar_Util.string_of_int uu____22213  in
                   let uu____22219 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____22220 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____22212 uu____22219 uu____22220)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____22226,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____22275  ->
                     let uu____22276 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____22276);
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
               let uu____22312 =
                 let uu___182_22313 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___182_22313.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___182_22313.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____22312
           | (Arg (Univ uu____22314,uu____22315,uu____22316))::uu____22317 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____22320,uu____22321))::uu____22322 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____22337,uu____22338),aq,r))::stack1
               when
               let uu____22388 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____22388 ->
               let t2 =
                 let uu____22392 =
                   let uu____22397 =
                     let uu____22398 = closure_as_term cfg env_arg tm  in
                     (uu____22398, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____22397  in
                 uu____22392 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____22404),aq,r))::stack1 ->
               (log cfg
                  (fun uu____22457  ->
                     let uu____22458 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____22458);
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
                  (let uu____22468 = FStar_ST.op_Bang m  in
                   match uu____22468 with
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
                   | FStar_Pervasives_Native.Some (uu____22609,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____22660 =
                 log cfg
                   (fun uu____22664  ->
                      let uu____22665 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____22665);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____22669 =
                 let uu____22670 = FStar_Syntax_Subst.compress t1  in
                 uu____22670.FStar_Syntax_Syntax.n  in
               (match uu____22669 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____22697 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____22697  in
                    (log cfg
                       (fun uu____22701  ->
                          let uu____22702 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____22702);
                     (let uu____22703 = FStar_List.tl stack  in
                      norm cfg env1 uu____22703 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____22704);
                       FStar_Syntax_Syntax.pos = uu____22705;
                       FStar_Syntax_Syntax.vars = uu____22706;_},(e,uu____22708)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____22737 when
                    (cfg.steps).primops ->
                    let uu____22752 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____22752 with
                     | (hd1,args) ->
                         let uu____22789 =
                           let uu____22790 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____22790.FStar_Syntax_Syntax.n  in
                         (match uu____22789 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____22794 = find_prim_step cfg fv  in
                              (match uu____22794 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____22797; arity = uu____22798;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____22800;
                                     requires_binder_substitution =
                                       uu____22801;
                                     interpretation = uu____22802;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____22817 -> fallback " (3)" ())
                          | uu____22820 -> fallback " (4)" ()))
                | uu____22821 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____22842  ->
                     let uu____22843 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____22843);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____22852 =
                   log cfg1
                     (fun uu____22857  ->
                        let uu____22858 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____22859 =
                          let uu____22860 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____22877  ->
                                    match uu____22877 with
                                    | (p,uu____22887,uu____22888) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____22860
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____22858 uu____22859);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___91_22905  ->
                                match uu___91_22905 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____22906 -> false))
                         in
                      let steps =
                        let uu___183_22908 = cfg1.steps  in
                        {
                          beta = (uu___183_22908.beta);
                          iota = (uu___183_22908.iota);
                          zeta = false;
                          weak = (uu___183_22908.weak);
                          hnf = (uu___183_22908.hnf);
                          primops = (uu___183_22908.primops);
                          do_not_unfold_pure_lets =
                            (uu___183_22908.do_not_unfold_pure_lets);
                          unfold_until = FStar_Pervasives_Native.None;
                          unfold_only = FStar_Pervasives_Native.None;
                          unfold_fully = (uu___183_22908.unfold_fully);
                          unfold_attr = FStar_Pervasives_Native.None;
                          unfold_tac = false;
                          pure_subterms_within_computations =
                            (uu___183_22908.pure_subterms_within_computations);
                          simplify = (uu___183_22908.simplify);
                          erase_universes = (uu___183_22908.erase_universes);
                          allow_unbound_universes =
                            (uu___183_22908.allow_unbound_universes);
                          reify_ = (uu___183_22908.reify_);
                          compress_uvars = (uu___183_22908.compress_uvars);
                          no_full_norm = (uu___183_22908.no_full_norm);
                          check_no_uvars = (uu___183_22908.check_no_uvars);
                          unmeta = (uu___183_22908.unmeta);
                          unascribe = (uu___183_22908.unascribe);
                          in_full_norm_request =
                            (uu___183_22908.in_full_norm_request);
                          weakly_reduce_scrutinee =
                            (uu___183_22908.weakly_reduce_scrutinee)
                        }  in
                      let uu___184_22913 = cfg1  in
                      {
                        steps;
                        tcenv = (uu___184_22913.tcenv);
                        debug = (uu___184_22913.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___184_22913.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___184_22913.memoize_lazy);
                        normalize_pure_lets =
                          (uu___184_22913.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____22953 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____22974 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____23034  ->
                                    fun uu____23035  ->
                                      match (uu____23034, uu____23035) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____23126 = norm_pat env3 p1
                                             in
                                          (match uu____23126 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____22974 with
                           | (pats1,env3) ->
                               ((let uu___185_23208 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___185_23208.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___186_23227 = x  in
                            let uu____23228 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___186_23227.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___186_23227.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23228
                            }  in
                          ((let uu___187_23242 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___187_23242.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___188_23253 = x  in
                            let uu____23254 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___188_23253.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___188_23253.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23254
                            }  in
                          ((let uu___189_23268 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___189_23268.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___190_23284 = x  in
                            let uu____23285 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___190_23284.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___190_23284.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____23285
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___191_23292 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___191_23292.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____23302 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____23316 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____23316 with
                                  | (p,wopt,e) ->
                                      let uu____23336 = norm_pat env1 p  in
                                      (match uu____23336 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____23361 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____23361
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____23368 =
                        ((((cfg1.steps).iota &&
                             (Prims.op_Negation (cfg1.steps).weak))
                            &&
                            (Prims.op_Negation (cfg1.steps).compress_uvars))
                           && (cfg1.steps).weakly_reduce_scrutinee)
                          && (maybe_weakly_reduced scrutinee)
                         in
                      if uu____23368
                      then
                        norm
                          (let uu___192_23371 = cfg1  in
                           {
                             steps =
                               (let uu___193_23374 = cfg1.steps  in
                                {
                                  beta = (uu___193_23374.beta);
                                  iota = (uu___193_23374.iota);
                                  zeta = (uu___193_23374.zeta);
                                  weak = (uu___193_23374.weak);
                                  hnf = (uu___193_23374.hnf);
                                  primops = (uu___193_23374.primops);
                                  do_not_unfold_pure_lets =
                                    (uu___193_23374.do_not_unfold_pure_lets);
                                  unfold_until =
                                    (uu___193_23374.unfold_until);
                                  unfold_only = (uu___193_23374.unfold_only);
                                  unfold_fully =
                                    (uu___193_23374.unfold_fully);
                                  unfold_attr = (uu___193_23374.unfold_attr);
                                  unfold_tac = (uu___193_23374.unfold_tac);
                                  pure_subterms_within_computations =
                                    (uu___193_23374.pure_subterms_within_computations);
                                  simplify = (uu___193_23374.simplify);
                                  erase_universes =
                                    (uu___193_23374.erase_universes);
                                  allow_unbound_universes =
                                    (uu___193_23374.allow_unbound_universes);
                                  reify_ = (uu___193_23374.reify_);
                                  compress_uvars =
                                    (uu___193_23374.compress_uvars);
                                  no_full_norm =
                                    (uu___193_23374.no_full_norm);
                                  check_no_uvars =
                                    (uu___193_23374.check_no_uvars);
                                  unmeta = (uu___193_23374.unmeta);
                                  unascribe = (uu___193_23374.unascribe);
                                  in_full_norm_request =
                                    (uu___193_23374.in_full_norm_request);
                                  weakly_reduce_scrutinee = false
                                });
                             tcenv = (uu___192_23371.tcenv);
                             debug = (uu___192_23371.debug);
                             delta_level = (uu___192_23371.delta_level);
                             primitive_steps =
                               (uu___192_23371.primitive_steps);
                             strong = (uu___192_23371.strong);
                             memoize_lazy = (uu___192_23371.memoize_lazy);
                             normalize_pure_lets =
                               (uu___192_23371.normalize_pure_lets)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____23376 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____23376)
                    in
                 let rec is_cons head1 =
                   let uu____23383 =
                     let uu____23384 = FStar_Syntax_Subst.compress head1  in
                     uu____23384.FStar_Syntax_Syntax.n  in
                   match uu____23383 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____23388) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____23393 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____23394;
                         FStar_Syntax_Syntax.fv_delta = uu____23395;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____23396;
                         FStar_Syntax_Syntax.fv_delta = uu____23397;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____23398);_}
                       -> true
                   | uu____23405 -> false  in
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
                   let uu____23566 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____23566 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____23653 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____23692 ->
                                 let uu____23693 =
                                   let uu____23694 = is_cons head1  in
                                   Prims.op_Negation uu____23694  in
                                 FStar_Util.Inr uu____23693)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____23719 =
                              let uu____23720 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____23720.FStar_Syntax_Syntax.n  in
                            (match uu____23719 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____23738 ->
                                 let uu____23739 =
                                   let uu____23740 = is_cons head1  in
                                   Prims.op_Negation uu____23740  in
                                 FStar_Util.Inr uu____23739))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____23809)::rest_a,(p1,uu____23812)::rest_p) ->
                       let uu____23856 = matches_pat t2 p1  in
                       (match uu____23856 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____23905 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____24015 = matches_pat scrutinee1 p1  in
                       (match uu____24015 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____24055  ->
                                  let uu____24056 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____24057 =
                                    let uu____24058 =
                                      FStar_List.map
                                        (fun uu____24068  ->
                                           match uu____24068 with
                                           | (uu____24073,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____24058
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____24056 uu____24057);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____24105  ->
                                       match uu____24105 with
                                       | (bv,t2) ->
                                           let uu____24128 =
                                             let uu____24135 =
                                               let uu____24138 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____24138
                                                in
                                             let uu____24139 =
                                               let uu____24140 =
                                                 let uu____24171 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____24171, false)
                                                  in
                                               Clos uu____24140  in
                                             (uu____24135, uu____24139)  in
                                           uu____24128 :: env2) env1 s
                                 in
                              let uu____24288 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____24288)))
                    in
                 if (cfg1.steps).iota
                 then matches scrutinee branches
                 else norm_and_rebuild_match ())))

let plugins :
  (primitive_step -> unit,unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____24315 =
      let uu____24318 = FStar_ST.op_Bang plugins  in p :: uu____24318  in
    FStar_ST.op_Colon_Equals plugins uu____24315  in
  let retrieve uu____24426 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let register_plugin : primitive_step -> unit =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let retrieve_plugins : unit -> primitive_step Prims.list =
  fun uu____24503  -> FStar_Pervasives_Native.snd plugins () 
let config' :
  primitive_step Prims.list ->
    step Prims.list -> FStar_TypeChecker_Env.env -> cfg
  =
  fun psteps  ->
    fun s  ->
      fun e  ->
        let d =
          FStar_All.pipe_right s
            (FStar_List.collect
               (fun uu___92_24544  ->
                  match uu___92_24544 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____24548 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____24554 -> d  in
        let uu____24557 = to_fsteps s  in
        let uu____24558 =
          let uu____24559 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____24560 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____24561 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____24562 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____24563 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____24559;
            primop = uu____24560;
            b380 = uu____24561;
            norm_delayed = uu____24562;
            print_normalized = uu____24563
          }  in
        let uu____24564 =
          let uu____24567 =
            let uu____24570 = retrieve_plugins ()  in
            FStar_List.append uu____24570 psteps  in
          add_steps built_in_primitive_steps uu____24567  in
        let uu____24573 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____24575 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____24575)
           in
        {
          steps = uu____24557;
          tcenv = e;
          debug = uu____24558;
          delta_level = d1;
          primitive_steps = uu____24564;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____24573
        }
  
let config : step Prims.list -> FStar_TypeChecker_Env.env -> cfg =
  fun s  -> fun e  -> config' [] s e 
let normalize_with_primitive_steps :
  primitive_step Prims.list ->
    step Prims.list ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun ps  ->
    fun s  -> fun e  -> fun t  -> let c = config' ps s e  in norm c [] [] t
  
let normalize :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t 
let normalize_comp :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun e  ->
      fun t  -> let uu____24657 = config s e  in norm_comp uu____24657 [] t
  
let normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe
  =
  fun env  ->
    fun u  ->
      let uu____24674 = config [] env  in norm_universe uu____24674 [] u
  
let ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp
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
        let uu____24698 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24698  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____24705 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___194_24724 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___194_24724.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___194_24724.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____24731 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____24731
          then
            let ct1 =
              let uu____24733 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____24733 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____24740 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____24740
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___195_24744 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___195_24744.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___195_24744.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___195_24744.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___196_24746 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___196_24746.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___196_24746.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___196_24746.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___196_24746.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___197_24747 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___197_24747.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___197_24747.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____24749 -> c
  
let ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp
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
        let uu____24767 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____24767  in
      let uu____24774 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____24774
      then
        let uu____24775 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____24775 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____24781  ->
                 let uu____24782 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____24782)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____24803 =
                let uu____24808 =
                  let uu____24809 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____24809
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____24808)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____24803);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____24824 = config [AllowUnboundUniverses] env  in
          norm_comp uu____24824 [] c
        with
        | e ->
            ((let uu____24837 =
                let uu____24842 =
                  let uu____24843 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____24843
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____24842)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____24837);
             c)
         in
      FStar_Syntax_Print.comp_to_string' env.FStar_TypeChecker_Env.dsenv c1
  
let normalize_refinement :
  steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
                   let uu____24888 =
                     let uu____24889 =
                       let uu____24896 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____24896)  in
                     FStar_Syntax_Syntax.Tm_refine uu____24889  in
                   mk uu____24888 t01.FStar_Syntax_Syntax.pos
               | uu____24901 -> t2)
          | uu____24902 -> t2  in
        aux t
  
let unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      normalize
        [Primops;
        Weak;
        HNF;
        UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
        Beta] env t
  
let reduce_or_remove_uvar_solutions :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
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
  
let reduce_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t 
let remove_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t 
let eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____24966 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____24966 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____24995 ->
                 let uu____25002 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____25002 with
                  | (actuals,uu____25012,uu____25013) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____25027 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____25027 with
                         | (binders,args) ->
                             let uu____25044 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____25044
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
  
let eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____25056 ->
          let uu____25057 = FStar_Syntax_Util.head_and_args t  in
          (match uu____25057 with
           | (head1,args) ->
               let uu____25094 =
                 let uu____25095 = FStar_Syntax_Subst.compress head1  in
                 uu____25095.FStar_Syntax_Syntax.n  in
               (match uu____25094 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____25098,thead) ->
                    let uu____25124 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____25124 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____25166 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___202_25174 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___202_25174.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___202_25174.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___202_25174.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___202_25174.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___202_25174.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___202_25174.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___202_25174.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___202_25174.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___202_25174.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___202_25174.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___202_25174.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___202_25174.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___202_25174.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___202_25174.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___202_25174.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___202_25174.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___202_25174.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___202_25174.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___202_25174.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___202_25174.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___202_25174.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___202_25174.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___202_25174.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___202_25174.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___202_25174.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___202_25174.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___202_25174.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___202_25174.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___202_25174.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___202_25174.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___202_25174.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___202_25174.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___202_25174.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___202_25174.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____25166 with
                            | (uu____25175,ty,uu____25177) ->
                                eta_expand_with_type env t ty))
                | uu____25178 ->
                    let uu____25179 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___203_25187 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___203_25187.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___203_25187.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___203_25187.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___203_25187.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___203_25187.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___203_25187.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___203_25187.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___203_25187.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___203_25187.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___203_25187.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___203_25187.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___203_25187.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___203_25187.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___203_25187.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___203_25187.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___203_25187.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___203_25187.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___203_25187.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___203_25187.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___203_25187.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___203_25187.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___203_25187.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___203_25187.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___203_25187.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___203_25187.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___203_25187.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___203_25187.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___203_25187.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___203_25187.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___203_25187.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___203_25187.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___203_25187.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___203_25187.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___203_25187.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____25179 with
                     | (uu____25188,ty,uu____25190) ->
                         eta_expand_with_type env t ty)))
  
let rec elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos
       in
    let t1 = FStar_Syntax_Subst.compress t  in
    let elim_bv x =
      let uu___204_25263 = x  in
      let uu____25264 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___204_25263.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___204_25263.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____25264
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____25267 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____25292 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____25293 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____25294 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____25295 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____25302 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____25303 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____25304 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___205_25334 = rc  in
          let uu____25335 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____25342 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___205_25334.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____25335;
            FStar_Syntax_Syntax.residual_flags = uu____25342
          }  in
        let uu____25345 =
          let uu____25346 =
            let uu____25363 = elim_delayed_subst_binders bs  in
            let uu____25370 = elim_delayed_subst_term t2  in
            let uu____25371 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____25363, uu____25370, uu____25371)  in
          FStar_Syntax_Syntax.Tm_abs uu____25346  in
        mk1 uu____25345
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____25400 =
          let uu____25401 =
            let uu____25414 = elim_delayed_subst_binders bs  in
            let uu____25421 = elim_delayed_subst_comp c  in
            (uu____25414, uu____25421)  in
          FStar_Syntax_Syntax.Tm_arrow uu____25401  in
        mk1 uu____25400
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____25434 =
          let uu____25435 =
            let uu____25442 = elim_bv bv  in
            let uu____25443 = elim_delayed_subst_term phi  in
            (uu____25442, uu____25443)  in
          FStar_Syntax_Syntax.Tm_refine uu____25435  in
        mk1 uu____25434
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____25466 =
          let uu____25467 =
            let uu____25482 = elim_delayed_subst_term t2  in
            let uu____25483 = elim_delayed_subst_args args  in
            (uu____25482, uu____25483)  in
          FStar_Syntax_Syntax.Tm_app uu____25467  in
        mk1 uu____25466
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___206_25549 = p  in
              let uu____25550 =
                let uu____25551 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____25551  in
              {
                FStar_Syntax_Syntax.v = uu____25550;
                FStar_Syntax_Syntax.p =
                  (uu___206_25549.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___207_25553 = p  in
              let uu____25554 =
                let uu____25555 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____25555  in
              {
                FStar_Syntax_Syntax.v = uu____25554;
                FStar_Syntax_Syntax.p =
                  (uu___207_25553.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___208_25562 = p  in
              let uu____25563 =
                let uu____25564 =
                  let uu____25571 = elim_bv x  in
                  let uu____25572 = elim_delayed_subst_term t0  in
                  (uu____25571, uu____25572)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____25564  in
              {
                FStar_Syntax_Syntax.v = uu____25563;
                FStar_Syntax_Syntax.p =
                  (uu___208_25562.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___209_25591 = p  in
              let uu____25592 =
                let uu____25593 =
                  let uu____25606 =
                    FStar_List.map
                      (fun uu____25629  ->
                         match uu____25629 with
                         | (x,b) ->
                             let uu____25642 = elim_pat x  in
                             (uu____25642, b)) pats
                     in
                  (fv, uu____25606)  in
                FStar_Syntax_Syntax.Pat_cons uu____25593  in
              {
                FStar_Syntax_Syntax.v = uu____25592;
                FStar_Syntax_Syntax.p =
                  (uu___209_25591.FStar_Syntax_Syntax.p)
              }
          | uu____25655 -> p  in
        let elim_branch uu____25679 =
          match uu____25679 with
          | (pat,wopt,t3) ->
              let uu____25705 = elim_pat pat  in
              let uu____25708 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____25711 = elim_delayed_subst_term t3  in
              (uu____25705, uu____25708, uu____25711)
           in
        let uu____25716 =
          let uu____25717 =
            let uu____25740 = elim_delayed_subst_term t2  in
            let uu____25741 = FStar_List.map elim_branch branches  in
            (uu____25740, uu____25741)  in
          FStar_Syntax_Syntax.Tm_match uu____25717  in
        mk1 uu____25716
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____25852 =
          match uu____25852 with
          | (tc,topt) ->
              let uu____25887 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____25897 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____25897
                | FStar_Util.Inr c ->
                    let uu____25899 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____25899
                 in
              let uu____25900 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____25887, uu____25900)
           in
        let uu____25909 =
          let uu____25910 =
            let uu____25937 = elim_delayed_subst_term t2  in
            let uu____25938 = elim_ascription a  in
            (uu____25937, uu____25938, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____25910  in
        mk1 uu____25909
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___210_25985 = lb  in
          let uu____25986 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____25989 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___210_25985.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___210_25985.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____25986;
            FStar_Syntax_Syntax.lbeff =
              (uu___210_25985.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____25989;
            FStar_Syntax_Syntax.lbattrs =
              (uu___210_25985.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___210_25985.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____25992 =
          let uu____25993 =
            let uu____26006 =
              let uu____26013 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____26013)  in
            let uu____26022 = elim_delayed_subst_term t2  in
            (uu____26006, uu____26022)  in
          FStar_Syntax_Syntax.Tm_let uu____25993  in
        mk1 uu____25992
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____26055 =
          let uu____26056 =
            let uu____26073 = elim_delayed_subst_term t2  in
            (uv, uu____26073)  in
          FStar_Syntax_Syntax.Tm_uvar uu____26056  in
        mk1 uu____26055
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____26091 =
          let uu____26092 =
            let uu____26099 = elim_delayed_subst_term tm  in
            (uu____26099, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____26092  in
        mk1 uu____26091
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____26106 =
          let uu____26107 =
            let uu____26114 = elim_delayed_subst_term t2  in
            let uu____26115 = elim_delayed_subst_meta md  in
            (uu____26114, uu____26115)  in
          FStar_Syntax_Syntax.Tm_meta uu____26107  in
        mk1 uu____26106

and elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_26122  ->
         match uu___93_26122 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____26126 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____26126
         | f -> f) flags1

and elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp =
  fun c  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos
       in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____26149 =
          let uu____26150 =
            let uu____26159 = elim_delayed_subst_term t  in
            (uu____26159, uopt)  in
          FStar_Syntax_Syntax.Total uu____26150  in
        mk1 uu____26149
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____26172 =
          let uu____26173 =
            let uu____26182 = elim_delayed_subst_term t  in
            (uu____26182, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____26173  in
        mk1 uu____26172
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___211_26187 = ct  in
          let uu____26188 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____26191 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____26200 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___211_26187.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___211_26187.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____26188;
            FStar_Syntax_Syntax.effect_args = uu____26191;
            FStar_Syntax_Syntax.flags = uu____26200
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata =
  fun uu___94_26203  ->
    match uu___94_26203 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____26215 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____26215
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____26248 =
          let uu____26255 = elim_delayed_subst_term t  in (m, uu____26255)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____26248
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____26263 =
          let uu____26272 = elim_delayed_subst_term t  in
          (m1, m2, uu____26272)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____26263
    | m -> m

and elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.map
      (fun uu____26295  ->
         match uu____26295 with
         | (t,q) ->
             let uu____26306 = elim_delayed_subst_term t  in (uu____26306, q))
      args

and elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun bs  ->
    FStar_List.map
      (fun uu____26326  ->
         match uu____26326 with
         | (x,q) ->
             let uu____26337 =
               let uu___212_26338 = x  in
               let uu____26339 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___212_26338.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___212_26338.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____26339
               }  in
             (uu____26337, q)) bs

let elim_uvars_aux_tc :
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
            FStar_Pervasives_Native.tuple3
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
            | (uu____26423,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____26429,FStar_Util.Inl t) ->
                let uu____26435 =
                  let uu____26442 =
                    let uu____26443 =
                      let uu____26456 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____26456)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____26443  in
                  FStar_Syntax_Syntax.mk uu____26442  in
                uu____26435 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____26460 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____26460 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____26488 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____26543 ->
                    let uu____26544 =
                      let uu____26553 =
                        let uu____26554 = FStar_Syntax_Subst.compress t4  in
                        uu____26554.FStar_Syntax_Syntax.n  in
                      (uu____26553, tc)  in
                    (match uu____26544 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____26579) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____26616) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____26655,FStar_Util.Inl uu____26656) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____26679 -> failwith "Impossible")
                 in
              (match uu____26488 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
  
let elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____26792 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____26792 with
          | (univ_names1,binders1,tc) ->
              let uu____26850 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____26850)
  
let elim_uvars_aux_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.comp'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____26893 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____26893 with
          | (univ_names1,binders1,tc) ->
              let uu____26953 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____26953)
  
let rec elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____26990 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____26990 with
           | (univ_names1,binders1,typ1) ->
               let uu___213_27018 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___213_27018.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___213_27018.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___213_27018.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___213_27018.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___214_27039 = s  in
          let uu____27040 =
            let uu____27041 =
              let uu____27050 = FStar_List.map (elim_uvars env) sigs  in
              (uu____27050, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____27041  in
          {
            FStar_Syntax_Syntax.sigel = uu____27040;
            FStar_Syntax_Syntax.sigrng =
              (uu___214_27039.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___214_27039.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___214_27039.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___214_27039.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____27067 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27067 with
           | (univ_names1,uu____27085,typ1) ->
               let uu___215_27099 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___215_27099.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___215_27099.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___215_27099.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___215_27099.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____27105 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____27105 with
           | (univ_names1,uu____27123,typ1) ->
               let uu___216_27137 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___216_27137.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___216_27137.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___216_27137.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___216_27137.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____27171 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____27171 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____27196 =
                            let uu____27197 =
                              let uu____27198 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____27198  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____27197
                             in
                          elim_delayed_subst_term uu____27196  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___217_27201 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___217_27201.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___217_27201.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___217_27201.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___217_27201.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___218_27202 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___218_27202.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___218_27202.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___218_27202.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___218_27202.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___219_27214 = s  in
          let uu____27215 =
            let uu____27216 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____27216  in
          {
            FStar_Syntax_Syntax.sigel = uu____27215;
            FStar_Syntax_Syntax.sigrng =
              (uu___219_27214.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___219_27214.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___219_27214.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___219_27214.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____27220 = elim_uvars_aux_t env us [] t  in
          (match uu____27220 with
           | (us1,uu____27238,t1) ->
               let uu___220_27252 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___220_27252.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___220_27252.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___220_27252.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___220_27252.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____27253 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____27255 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____27255 with
           | (univs1,binders,signature) ->
               let uu____27283 =
                 let uu____27292 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____27292 with
                 | (univs_opening,univs2) ->
                     let uu____27319 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____27319)
                  in
               (match uu____27283 with
                | (univs_opening,univs_closing) ->
                    let uu____27336 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____27342 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____27343 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____27342, uu____27343)  in
                    (match uu____27336 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____27367 =
                           match uu____27367 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____27385 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____27385 with
                                | (us1,t1) ->
                                    let uu____27396 =
                                      let uu____27401 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____27408 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____27401, uu____27408)  in
                                    (match uu____27396 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____27421 =
                                           let uu____27426 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____27435 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____27426, uu____27435)  in
                                         (match uu____27421 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____27451 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____27451
                                                 in
                                              let uu____27452 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____27452 with
                                               | (uu____27473,uu____27474,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____27489 =
                                                       let uu____27490 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____27490
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____27489
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____27497 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____27497 with
                           | (uu____27510,uu____27511,t1) -> t1  in
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
                             | uu____27573 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____27592 =
                               let uu____27593 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____27593.FStar_Syntax_Syntax.n  in
                             match uu____27592 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____27652 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____27683 =
                               let uu____27684 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____27684.FStar_Syntax_Syntax.n  in
                             match uu____27683 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____27705) ->
                                 let uu____27726 = destruct_action_body body
                                    in
                                 (match uu____27726 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____27771 ->
                                 let uu____27772 = destruct_action_body t  in
                                 (match uu____27772 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____27821 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____27821 with
                           | (action_univs,t) ->
                               let uu____27830 = destruct_action_typ_templ t
                                  in
                               (match uu____27830 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___221_27871 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___221_27871.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___221_27871.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___222_27873 = ed  in
                           let uu____27874 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____27875 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____27876 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____27877 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____27878 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____27879 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____27880 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____27881 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____27882 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____27883 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____27884 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____27885 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____27886 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____27887 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___222_27873.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___222_27873.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____27874;
                             FStar_Syntax_Syntax.bind_wp = uu____27875;
                             FStar_Syntax_Syntax.if_then_else = uu____27876;
                             FStar_Syntax_Syntax.ite_wp = uu____27877;
                             FStar_Syntax_Syntax.stronger = uu____27878;
                             FStar_Syntax_Syntax.close_wp = uu____27879;
                             FStar_Syntax_Syntax.assert_p = uu____27880;
                             FStar_Syntax_Syntax.assume_p = uu____27881;
                             FStar_Syntax_Syntax.null_wp = uu____27882;
                             FStar_Syntax_Syntax.trivial = uu____27883;
                             FStar_Syntax_Syntax.repr = uu____27884;
                             FStar_Syntax_Syntax.return_repr = uu____27885;
                             FStar_Syntax_Syntax.bind_repr = uu____27886;
                             FStar_Syntax_Syntax.actions = uu____27887;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___222_27873.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___223_27890 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___223_27890.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___223_27890.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___223_27890.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___223_27890.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_27909 =
            match uu___95_27909 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____27936 = elim_uvars_aux_t env us [] t  in
                (match uu____27936 with
                 | (us1,uu____27960,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___224_27979 = sub_eff  in
            let uu____27980 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____27983 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___224_27979.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___224_27979.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____27980;
              FStar_Syntax_Syntax.lift = uu____27983
            }  in
          let uu___225_27986 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___225_27986.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___225_27986.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___225_27986.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___225_27986.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____27996 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____27996 with
           | (univ_names1,binders1,comp1) ->
               let uu___226_28030 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___226_28030.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___226_28030.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___226_28030.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___226_28030.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____28041 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____28042 -> s
  
let erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  