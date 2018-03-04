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
  | NoDeltaSteps 
  | UnfoldUntil of FStar_Syntax_Syntax.delta_depth 
  | UnfoldOnly of FStar_Ident.lid Prims.list 
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
  fun projectee  -> match projectee with | Beta  -> true | uu____22 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____26 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____30 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____35 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____46 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____50 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____54 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____58 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____62 -> false
  
let (uu___is_NoDeltaSteps : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____66 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____71 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____85 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____103 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____114 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____118 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____122 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____126 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____130 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____134 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____138 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____142 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____146 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____150 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____154 -> false
  
type steps = step Prims.list[@@deriving show]
let cases :
  'Auu____162 'Auu____163 .
    ('Auu____163 -> 'Auu____162) ->
      'Auu____162 ->
        'Auu____163 FStar_Pervasives_Native.option -> 'Auu____162
  =
  fun f  ->
    fun d  ->
      fun uu___75_180  ->
        match uu___75_180 with
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
  no_delta_steps: Prims.bool ;
  unfold_until:
    FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option ;
  unfold_only: FStar_Ident.lid Prims.list FStar_Pervasives_Native.option ;
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
  unascribe: Prims.bool }[@@deriving show]
let (__proj__Mkfsteps__item__beta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__beta
  
let (__proj__Mkfsteps__item__iota : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__iota
  
let (__proj__Mkfsteps__item__zeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__zeta
  
let (__proj__Mkfsteps__item__weak : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__weak
  
let (__proj__Mkfsteps__item__hnf : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__hnf
  
let (__proj__Mkfsteps__item__primops : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__primops
  
let (__proj__Mkfsteps__item__no_delta_steps : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__no_delta_steps
  
let (__proj__Mkfsteps__item__unfold_until :
  fsteps -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_until
  
let (__proj__Mkfsteps__item__unfold_only :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_only
  
let (__proj__Mkfsteps__item__unfold_attr :
  fsteps ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_attr
  
let (__proj__Mkfsteps__item__unfold_tac : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unfold_tac
  
let (__proj__Mkfsteps__item__pure_subterms_within_computations :
  fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} ->
        __fname__pure_subterms_within_computations
  
let (__proj__Mkfsteps__item__simplify : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__simplify
  
let (__proj__Mkfsteps__item__erase_universes : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__erase_universes
  
let (__proj__Mkfsteps__item__allow_unbound_universes : fsteps -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__allow_unbound_universes
  
let (__proj__Mkfsteps__item__reify_ : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__reify_
  
let (__proj__Mkfsteps__item__compress_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__compress_uvars
  
let (__proj__Mkfsteps__item__no_full_norm : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__no_full_norm
  
let (__proj__Mkfsteps__item__check_no_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__check_no_uvars
  
let (__proj__Mkfsteps__item__unmeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unmeta
  
let (__proj__Mkfsteps__item__unascribe : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
        unfold_until = __fname__unfold_until;
        unfold_only = __fname__unfold_only;
        unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac;
        pure_subterms_within_computations =
          __fname__pure_subterms_within_computations;
        simplify = __fname__simplify;
        erase_universes = __fname__erase_universes;
        allow_unbound_universes = __fname__allow_unbound_universes;
        reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars;
        no_full_norm = __fname__no_full_norm;
        check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta;
        unascribe = __fname__unascribe;_} -> __fname__unascribe
  
let (default_steps : fsteps) =
  {
    beta = true;
    iota = true;
    zeta = true;
    weak = false;
    hnf = false;
    primops = false;
    no_delta_steps = false;
    unfold_until = FStar_Pervasives_Native.None;
    unfold_only = FStar_Pervasives_Native.None;
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
    unascribe = false
  } 
let (fstep_add_one : step -> fsteps -> fsteps) =
  fun s  ->
    fun fs  ->
      let add_opt x uu___76_1038 =
        match uu___76_1038 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___94_1058 = fs  in
          {
            beta = true;
            iota = (uu___94_1058.iota);
            zeta = (uu___94_1058.zeta);
            weak = (uu___94_1058.weak);
            hnf = (uu___94_1058.hnf);
            primops = (uu___94_1058.primops);
            no_delta_steps = (uu___94_1058.no_delta_steps);
            unfold_until = (uu___94_1058.unfold_until);
            unfold_only = (uu___94_1058.unfold_only);
            unfold_attr = (uu___94_1058.unfold_attr);
            unfold_tac = (uu___94_1058.unfold_tac);
            pure_subterms_within_computations =
              (uu___94_1058.pure_subterms_within_computations);
            simplify = (uu___94_1058.simplify);
            erase_universes = (uu___94_1058.erase_universes);
            allow_unbound_universes = (uu___94_1058.allow_unbound_universes);
            reify_ = (uu___94_1058.reify_);
            compress_uvars = (uu___94_1058.compress_uvars);
            no_full_norm = (uu___94_1058.no_full_norm);
            check_no_uvars = (uu___94_1058.check_no_uvars);
            unmeta = (uu___94_1058.unmeta);
            unascribe = (uu___94_1058.unascribe)
          }
      | Iota  ->
          let uu___95_1059 = fs  in
          {
            beta = (uu___95_1059.beta);
            iota = true;
            zeta = (uu___95_1059.zeta);
            weak = (uu___95_1059.weak);
            hnf = (uu___95_1059.hnf);
            primops = (uu___95_1059.primops);
            no_delta_steps = (uu___95_1059.no_delta_steps);
            unfold_until = (uu___95_1059.unfold_until);
            unfold_only = (uu___95_1059.unfold_only);
            unfold_attr = (uu___95_1059.unfold_attr);
            unfold_tac = (uu___95_1059.unfold_tac);
            pure_subterms_within_computations =
              (uu___95_1059.pure_subterms_within_computations);
            simplify = (uu___95_1059.simplify);
            erase_universes = (uu___95_1059.erase_universes);
            allow_unbound_universes = (uu___95_1059.allow_unbound_universes);
            reify_ = (uu___95_1059.reify_);
            compress_uvars = (uu___95_1059.compress_uvars);
            no_full_norm = (uu___95_1059.no_full_norm);
            check_no_uvars = (uu___95_1059.check_no_uvars);
            unmeta = (uu___95_1059.unmeta);
            unascribe = (uu___95_1059.unascribe)
          }
      | Zeta  ->
          let uu___96_1060 = fs  in
          {
            beta = (uu___96_1060.beta);
            iota = (uu___96_1060.iota);
            zeta = true;
            weak = (uu___96_1060.weak);
            hnf = (uu___96_1060.hnf);
            primops = (uu___96_1060.primops);
            no_delta_steps = (uu___96_1060.no_delta_steps);
            unfold_until = (uu___96_1060.unfold_until);
            unfold_only = (uu___96_1060.unfold_only);
            unfold_attr = (uu___96_1060.unfold_attr);
            unfold_tac = (uu___96_1060.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1060.pure_subterms_within_computations);
            simplify = (uu___96_1060.simplify);
            erase_universes = (uu___96_1060.erase_universes);
            allow_unbound_universes = (uu___96_1060.allow_unbound_universes);
            reify_ = (uu___96_1060.reify_);
            compress_uvars = (uu___96_1060.compress_uvars);
            no_full_norm = (uu___96_1060.no_full_norm);
            check_no_uvars = (uu___96_1060.check_no_uvars);
            unmeta = (uu___96_1060.unmeta);
            unascribe = (uu___96_1060.unascribe)
          }
      | Exclude (Beta ) ->
          let uu___97_1061 = fs  in
          {
            beta = false;
            iota = (uu___97_1061.iota);
            zeta = (uu___97_1061.zeta);
            weak = (uu___97_1061.weak);
            hnf = (uu___97_1061.hnf);
            primops = (uu___97_1061.primops);
            no_delta_steps = (uu___97_1061.no_delta_steps);
            unfold_until = (uu___97_1061.unfold_until);
            unfold_only = (uu___97_1061.unfold_only);
            unfold_attr = (uu___97_1061.unfold_attr);
            unfold_tac = (uu___97_1061.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1061.pure_subterms_within_computations);
            simplify = (uu___97_1061.simplify);
            erase_universes = (uu___97_1061.erase_universes);
            allow_unbound_universes = (uu___97_1061.allow_unbound_universes);
            reify_ = (uu___97_1061.reify_);
            compress_uvars = (uu___97_1061.compress_uvars);
            no_full_norm = (uu___97_1061.no_full_norm);
            check_no_uvars = (uu___97_1061.check_no_uvars);
            unmeta = (uu___97_1061.unmeta);
            unascribe = (uu___97_1061.unascribe)
          }
      | Exclude (Iota ) ->
          let uu___98_1062 = fs  in
          {
            beta = (uu___98_1062.beta);
            iota = false;
            zeta = (uu___98_1062.zeta);
            weak = (uu___98_1062.weak);
            hnf = (uu___98_1062.hnf);
            primops = (uu___98_1062.primops);
            no_delta_steps = (uu___98_1062.no_delta_steps);
            unfold_until = (uu___98_1062.unfold_until);
            unfold_only = (uu___98_1062.unfold_only);
            unfold_attr = (uu___98_1062.unfold_attr);
            unfold_tac = (uu___98_1062.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1062.pure_subterms_within_computations);
            simplify = (uu___98_1062.simplify);
            erase_universes = (uu___98_1062.erase_universes);
            allow_unbound_universes = (uu___98_1062.allow_unbound_universes);
            reify_ = (uu___98_1062.reify_);
            compress_uvars = (uu___98_1062.compress_uvars);
            no_full_norm = (uu___98_1062.no_full_norm);
            check_no_uvars = (uu___98_1062.check_no_uvars);
            unmeta = (uu___98_1062.unmeta);
            unascribe = (uu___98_1062.unascribe)
          }
      | Exclude (Zeta ) ->
          let uu___99_1063 = fs  in
          {
            beta = (uu___99_1063.beta);
            iota = (uu___99_1063.iota);
            zeta = false;
            weak = (uu___99_1063.weak);
            hnf = (uu___99_1063.hnf);
            primops = (uu___99_1063.primops);
            no_delta_steps = (uu___99_1063.no_delta_steps);
            unfold_until = (uu___99_1063.unfold_until);
            unfold_only = (uu___99_1063.unfold_only);
            unfold_attr = (uu___99_1063.unfold_attr);
            unfold_tac = (uu___99_1063.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1063.pure_subterms_within_computations);
            simplify = (uu___99_1063.simplify);
            erase_universes = (uu___99_1063.erase_universes);
            allow_unbound_universes = (uu___99_1063.allow_unbound_universes);
            reify_ = (uu___99_1063.reify_);
            compress_uvars = (uu___99_1063.compress_uvars);
            no_full_norm = (uu___99_1063.no_full_norm);
            check_no_uvars = (uu___99_1063.check_no_uvars);
            unmeta = (uu___99_1063.unmeta);
            unascribe = (uu___99_1063.unascribe)
          }
      | Exclude uu____1064 -> failwith "Bad exclude"
      | Weak  ->
          let uu___100_1065 = fs  in
          {
            beta = (uu___100_1065.beta);
            iota = (uu___100_1065.iota);
            zeta = (uu___100_1065.zeta);
            weak = true;
            hnf = (uu___100_1065.hnf);
            primops = (uu___100_1065.primops);
            no_delta_steps = (uu___100_1065.no_delta_steps);
            unfold_until = (uu___100_1065.unfold_until);
            unfold_only = (uu___100_1065.unfold_only);
            unfold_attr = (uu___100_1065.unfold_attr);
            unfold_tac = (uu___100_1065.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1065.pure_subterms_within_computations);
            simplify = (uu___100_1065.simplify);
            erase_universes = (uu___100_1065.erase_universes);
            allow_unbound_universes = (uu___100_1065.allow_unbound_universes);
            reify_ = (uu___100_1065.reify_);
            compress_uvars = (uu___100_1065.compress_uvars);
            no_full_norm = (uu___100_1065.no_full_norm);
            check_no_uvars = (uu___100_1065.check_no_uvars);
            unmeta = (uu___100_1065.unmeta);
            unascribe = (uu___100_1065.unascribe)
          }
      | HNF  ->
          let uu___101_1066 = fs  in
          {
            beta = (uu___101_1066.beta);
            iota = (uu___101_1066.iota);
            zeta = (uu___101_1066.zeta);
            weak = (uu___101_1066.weak);
            hnf = true;
            primops = (uu___101_1066.primops);
            no_delta_steps = (uu___101_1066.no_delta_steps);
            unfold_until = (uu___101_1066.unfold_until);
            unfold_only = (uu___101_1066.unfold_only);
            unfold_attr = (uu___101_1066.unfold_attr);
            unfold_tac = (uu___101_1066.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1066.pure_subterms_within_computations);
            simplify = (uu___101_1066.simplify);
            erase_universes = (uu___101_1066.erase_universes);
            allow_unbound_universes = (uu___101_1066.allow_unbound_universes);
            reify_ = (uu___101_1066.reify_);
            compress_uvars = (uu___101_1066.compress_uvars);
            no_full_norm = (uu___101_1066.no_full_norm);
            check_no_uvars = (uu___101_1066.check_no_uvars);
            unmeta = (uu___101_1066.unmeta);
            unascribe = (uu___101_1066.unascribe)
          }
      | Primops  ->
          let uu___102_1067 = fs  in
          {
            beta = (uu___102_1067.beta);
            iota = (uu___102_1067.iota);
            zeta = (uu___102_1067.zeta);
            weak = (uu___102_1067.weak);
            hnf = (uu___102_1067.hnf);
            primops = true;
            no_delta_steps = (uu___102_1067.no_delta_steps);
            unfold_until = (uu___102_1067.unfold_until);
            unfold_only = (uu___102_1067.unfold_only);
            unfold_attr = (uu___102_1067.unfold_attr);
            unfold_tac = (uu___102_1067.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1067.pure_subterms_within_computations);
            simplify = (uu___102_1067.simplify);
            erase_universes = (uu___102_1067.erase_universes);
            allow_unbound_universes = (uu___102_1067.allow_unbound_universes);
            reify_ = (uu___102_1067.reify_);
            compress_uvars = (uu___102_1067.compress_uvars);
            no_full_norm = (uu___102_1067.no_full_norm);
            check_no_uvars = (uu___102_1067.check_no_uvars);
            unmeta = (uu___102_1067.unmeta);
            unascribe = (uu___102_1067.unascribe)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | NoDeltaSteps  ->
          let uu___103_1068 = fs  in
          {
            beta = (uu___103_1068.beta);
            iota = (uu___103_1068.iota);
            zeta = (uu___103_1068.zeta);
            weak = (uu___103_1068.weak);
            hnf = (uu___103_1068.hnf);
            primops = (uu___103_1068.primops);
            no_delta_steps = true;
            unfold_until = (uu___103_1068.unfold_until);
            unfold_only = (uu___103_1068.unfold_only);
            unfold_attr = (uu___103_1068.unfold_attr);
            unfold_tac = (uu___103_1068.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1068.pure_subterms_within_computations);
            simplify = (uu___103_1068.simplify);
            erase_universes = (uu___103_1068.erase_universes);
            allow_unbound_universes = (uu___103_1068.allow_unbound_universes);
            reify_ = (uu___103_1068.reify_);
            compress_uvars = (uu___103_1068.compress_uvars);
            no_full_norm = (uu___103_1068.no_full_norm);
            check_no_uvars = (uu___103_1068.check_no_uvars);
            unmeta = (uu___103_1068.unmeta);
            unascribe = (uu___103_1068.unascribe)
          }
      | UnfoldUntil d ->
          let uu___104_1070 = fs  in
          {
            beta = (uu___104_1070.beta);
            iota = (uu___104_1070.iota);
            zeta = (uu___104_1070.zeta);
            weak = (uu___104_1070.weak);
            hnf = (uu___104_1070.hnf);
            primops = (uu___104_1070.primops);
            no_delta_steps = (uu___104_1070.no_delta_steps);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___104_1070.unfold_only);
            unfold_attr = (uu___104_1070.unfold_attr);
            unfold_tac = (uu___104_1070.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1070.pure_subterms_within_computations);
            simplify = (uu___104_1070.simplify);
            erase_universes = (uu___104_1070.erase_universes);
            allow_unbound_universes = (uu___104_1070.allow_unbound_universes);
            reify_ = (uu___104_1070.reify_);
            compress_uvars = (uu___104_1070.compress_uvars);
            no_full_norm = (uu___104_1070.no_full_norm);
            check_no_uvars = (uu___104_1070.check_no_uvars);
            unmeta = (uu___104_1070.unmeta);
            unascribe = (uu___104_1070.unascribe)
          }
      | UnfoldOnly lids ->
          let uu___105_1074 = fs  in
          {
            beta = (uu___105_1074.beta);
            iota = (uu___105_1074.iota);
            zeta = (uu___105_1074.zeta);
            weak = (uu___105_1074.weak);
            hnf = (uu___105_1074.hnf);
            primops = (uu___105_1074.primops);
            no_delta_steps = (uu___105_1074.no_delta_steps);
            unfold_until = (uu___105_1074.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___105_1074.unfold_attr);
            unfold_tac = (uu___105_1074.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1074.pure_subterms_within_computations);
            simplify = (uu___105_1074.simplify);
            erase_universes = (uu___105_1074.erase_universes);
            allow_unbound_universes = (uu___105_1074.allow_unbound_universes);
            reify_ = (uu___105_1074.reify_);
            compress_uvars = (uu___105_1074.compress_uvars);
            no_full_norm = (uu___105_1074.no_full_norm);
            check_no_uvars = (uu___105_1074.check_no_uvars);
            unmeta = (uu___105_1074.unmeta);
            unascribe = (uu___105_1074.unascribe)
          }
      | UnfoldAttr attr ->
          let uu___106_1078 = fs  in
          {
            beta = (uu___106_1078.beta);
            iota = (uu___106_1078.iota);
            zeta = (uu___106_1078.zeta);
            weak = (uu___106_1078.weak);
            hnf = (uu___106_1078.hnf);
            primops = (uu___106_1078.primops);
            no_delta_steps = (uu___106_1078.no_delta_steps);
            unfold_until = (uu___106_1078.unfold_until);
            unfold_only = (uu___106_1078.unfold_only);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___106_1078.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1078.pure_subterms_within_computations);
            simplify = (uu___106_1078.simplify);
            erase_universes = (uu___106_1078.erase_universes);
            allow_unbound_universes = (uu___106_1078.allow_unbound_universes);
            reify_ = (uu___106_1078.reify_);
            compress_uvars = (uu___106_1078.compress_uvars);
            no_full_norm = (uu___106_1078.no_full_norm);
            check_no_uvars = (uu___106_1078.check_no_uvars);
            unmeta = (uu___106_1078.unmeta);
            unascribe = (uu___106_1078.unascribe)
          }
      | UnfoldTac  ->
          let uu___107_1079 = fs  in
          {
            beta = (uu___107_1079.beta);
            iota = (uu___107_1079.iota);
            zeta = (uu___107_1079.zeta);
            weak = (uu___107_1079.weak);
            hnf = (uu___107_1079.hnf);
            primops = (uu___107_1079.primops);
            no_delta_steps = (uu___107_1079.no_delta_steps);
            unfold_until = (uu___107_1079.unfold_until);
            unfold_only = (uu___107_1079.unfold_only);
            unfold_attr = (uu___107_1079.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___107_1079.pure_subterms_within_computations);
            simplify = (uu___107_1079.simplify);
            erase_universes = (uu___107_1079.erase_universes);
            allow_unbound_universes = (uu___107_1079.allow_unbound_universes);
            reify_ = (uu___107_1079.reify_);
            compress_uvars = (uu___107_1079.compress_uvars);
            no_full_norm = (uu___107_1079.no_full_norm);
            check_no_uvars = (uu___107_1079.check_no_uvars);
            unmeta = (uu___107_1079.unmeta);
            unascribe = (uu___107_1079.unascribe)
          }
      | PureSubtermsWithinComputations  ->
          let uu___108_1080 = fs  in
          {
            beta = (uu___108_1080.beta);
            iota = (uu___108_1080.iota);
            zeta = (uu___108_1080.zeta);
            weak = (uu___108_1080.weak);
            hnf = (uu___108_1080.hnf);
            primops = (uu___108_1080.primops);
            no_delta_steps = (uu___108_1080.no_delta_steps);
            unfold_until = (uu___108_1080.unfold_until);
            unfold_only = (uu___108_1080.unfold_only);
            unfold_attr = (uu___108_1080.unfold_attr);
            unfold_tac = (uu___108_1080.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___108_1080.simplify);
            erase_universes = (uu___108_1080.erase_universes);
            allow_unbound_universes = (uu___108_1080.allow_unbound_universes);
            reify_ = (uu___108_1080.reify_);
            compress_uvars = (uu___108_1080.compress_uvars);
            no_full_norm = (uu___108_1080.no_full_norm);
            check_no_uvars = (uu___108_1080.check_no_uvars);
            unmeta = (uu___108_1080.unmeta);
            unascribe = (uu___108_1080.unascribe)
          }
      | Simplify  ->
          let uu___109_1081 = fs  in
          {
            beta = (uu___109_1081.beta);
            iota = (uu___109_1081.iota);
            zeta = (uu___109_1081.zeta);
            weak = (uu___109_1081.weak);
            hnf = (uu___109_1081.hnf);
            primops = (uu___109_1081.primops);
            no_delta_steps = (uu___109_1081.no_delta_steps);
            unfold_until = (uu___109_1081.unfold_until);
            unfold_only = (uu___109_1081.unfold_only);
            unfold_attr = (uu___109_1081.unfold_attr);
            unfold_tac = (uu___109_1081.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1081.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___109_1081.erase_universes);
            allow_unbound_universes = (uu___109_1081.allow_unbound_universes);
            reify_ = (uu___109_1081.reify_);
            compress_uvars = (uu___109_1081.compress_uvars);
            no_full_norm = (uu___109_1081.no_full_norm);
            check_no_uvars = (uu___109_1081.check_no_uvars);
            unmeta = (uu___109_1081.unmeta);
            unascribe = (uu___109_1081.unascribe)
          }
      | EraseUniverses  ->
          let uu___110_1082 = fs  in
          {
            beta = (uu___110_1082.beta);
            iota = (uu___110_1082.iota);
            zeta = (uu___110_1082.zeta);
            weak = (uu___110_1082.weak);
            hnf = (uu___110_1082.hnf);
            primops = (uu___110_1082.primops);
            no_delta_steps = (uu___110_1082.no_delta_steps);
            unfold_until = (uu___110_1082.unfold_until);
            unfold_only = (uu___110_1082.unfold_only);
            unfold_attr = (uu___110_1082.unfold_attr);
            unfold_tac = (uu___110_1082.unfold_tac);
            pure_subterms_within_computations =
              (uu___110_1082.pure_subterms_within_computations);
            simplify = (uu___110_1082.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___110_1082.allow_unbound_universes);
            reify_ = (uu___110_1082.reify_);
            compress_uvars = (uu___110_1082.compress_uvars);
            no_full_norm = (uu___110_1082.no_full_norm);
            check_no_uvars = (uu___110_1082.check_no_uvars);
            unmeta = (uu___110_1082.unmeta);
            unascribe = (uu___110_1082.unascribe)
          }
      | AllowUnboundUniverses  ->
          let uu___111_1083 = fs  in
          {
            beta = (uu___111_1083.beta);
            iota = (uu___111_1083.iota);
            zeta = (uu___111_1083.zeta);
            weak = (uu___111_1083.weak);
            hnf = (uu___111_1083.hnf);
            primops = (uu___111_1083.primops);
            no_delta_steps = (uu___111_1083.no_delta_steps);
            unfold_until = (uu___111_1083.unfold_until);
            unfold_only = (uu___111_1083.unfold_only);
            unfold_attr = (uu___111_1083.unfold_attr);
            unfold_tac = (uu___111_1083.unfold_tac);
            pure_subterms_within_computations =
              (uu___111_1083.pure_subterms_within_computations);
            simplify = (uu___111_1083.simplify);
            erase_universes = (uu___111_1083.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___111_1083.reify_);
            compress_uvars = (uu___111_1083.compress_uvars);
            no_full_norm = (uu___111_1083.no_full_norm);
            check_no_uvars = (uu___111_1083.check_no_uvars);
            unmeta = (uu___111_1083.unmeta);
            unascribe = (uu___111_1083.unascribe)
          }
      | Reify  ->
          let uu___112_1084 = fs  in
          {
            beta = (uu___112_1084.beta);
            iota = (uu___112_1084.iota);
            zeta = (uu___112_1084.zeta);
            weak = (uu___112_1084.weak);
            hnf = (uu___112_1084.hnf);
            primops = (uu___112_1084.primops);
            no_delta_steps = (uu___112_1084.no_delta_steps);
            unfold_until = (uu___112_1084.unfold_until);
            unfold_only = (uu___112_1084.unfold_only);
            unfold_attr = (uu___112_1084.unfold_attr);
            unfold_tac = (uu___112_1084.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1084.pure_subterms_within_computations);
            simplify = (uu___112_1084.simplify);
            erase_universes = (uu___112_1084.erase_universes);
            allow_unbound_universes = (uu___112_1084.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___112_1084.compress_uvars);
            no_full_norm = (uu___112_1084.no_full_norm);
            check_no_uvars = (uu___112_1084.check_no_uvars);
            unmeta = (uu___112_1084.unmeta);
            unascribe = (uu___112_1084.unascribe)
          }
      | CompressUvars  ->
          let uu___113_1085 = fs  in
          {
            beta = (uu___113_1085.beta);
            iota = (uu___113_1085.iota);
            zeta = (uu___113_1085.zeta);
            weak = (uu___113_1085.weak);
            hnf = (uu___113_1085.hnf);
            primops = (uu___113_1085.primops);
            no_delta_steps = (uu___113_1085.no_delta_steps);
            unfold_until = (uu___113_1085.unfold_until);
            unfold_only = (uu___113_1085.unfold_only);
            unfold_attr = (uu___113_1085.unfold_attr);
            unfold_tac = (uu___113_1085.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1085.pure_subterms_within_computations);
            simplify = (uu___113_1085.simplify);
            erase_universes = (uu___113_1085.erase_universes);
            allow_unbound_universes = (uu___113_1085.allow_unbound_universes);
            reify_ = (uu___113_1085.reify_);
            compress_uvars = true;
            no_full_norm = (uu___113_1085.no_full_norm);
            check_no_uvars = (uu___113_1085.check_no_uvars);
            unmeta = (uu___113_1085.unmeta);
            unascribe = (uu___113_1085.unascribe)
          }
      | NoFullNorm  ->
          let uu___114_1086 = fs  in
          {
            beta = (uu___114_1086.beta);
            iota = (uu___114_1086.iota);
            zeta = (uu___114_1086.zeta);
            weak = (uu___114_1086.weak);
            hnf = (uu___114_1086.hnf);
            primops = (uu___114_1086.primops);
            no_delta_steps = (uu___114_1086.no_delta_steps);
            unfold_until = (uu___114_1086.unfold_until);
            unfold_only = (uu___114_1086.unfold_only);
            unfold_attr = (uu___114_1086.unfold_attr);
            unfold_tac = (uu___114_1086.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1086.pure_subterms_within_computations);
            simplify = (uu___114_1086.simplify);
            erase_universes = (uu___114_1086.erase_universes);
            allow_unbound_universes = (uu___114_1086.allow_unbound_universes);
            reify_ = (uu___114_1086.reify_);
            compress_uvars = (uu___114_1086.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___114_1086.check_no_uvars);
            unmeta = (uu___114_1086.unmeta);
            unascribe = (uu___114_1086.unascribe)
          }
      | CheckNoUvars  ->
          let uu___115_1087 = fs  in
          {
            beta = (uu___115_1087.beta);
            iota = (uu___115_1087.iota);
            zeta = (uu___115_1087.zeta);
            weak = (uu___115_1087.weak);
            hnf = (uu___115_1087.hnf);
            primops = (uu___115_1087.primops);
            no_delta_steps = (uu___115_1087.no_delta_steps);
            unfold_until = (uu___115_1087.unfold_until);
            unfold_only = (uu___115_1087.unfold_only);
            unfold_attr = (uu___115_1087.unfold_attr);
            unfold_tac = (uu___115_1087.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1087.pure_subterms_within_computations);
            simplify = (uu___115_1087.simplify);
            erase_universes = (uu___115_1087.erase_universes);
            allow_unbound_universes = (uu___115_1087.allow_unbound_universes);
            reify_ = (uu___115_1087.reify_);
            compress_uvars = (uu___115_1087.compress_uvars);
            no_full_norm = (uu___115_1087.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___115_1087.unmeta);
            unascribe = (uu___115_1087.unascribe)
          }
      | Unmeta  ->
          let uu___116_1088 = fs  in
          {
            beta = (uu___116_1088.beta);
            iota = (uu___116_1088.iota);
            zeta = (uu___116_1088.zeta);
            weak = (uu___116_1088.weak);
            hnf = (uu___116_1088.hnf);
            primops = (uu___116_1088.primops);
            no_delta_steps = (uu___116_1088.no_delta_steps);
            unfold_until = (uu___116_1088.unfold_until);
            unfold_only = (uu___116_1088.unfold_only);
            unfold_attr = (uu___116_1088.unfold_attr);
            unfold_tac = (uu___116_1088.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1088.pure_subterms_within_computations);
            simplify = (uu___116_1088.simplify);
            erase_universes = (uu___116_1088.erase_universes);
            allow_unbound_universes = (uu___116_1088.allow_unbound_universes);
            reify_ = (uu___116_1088.reify_);
            compress_uvars = (uu___116_1088.compress_uvars);
            no_full_norm = (uu___116_1088.no_full_norm);
            check_no_uvars = (uu___116_1088.check_no_uvars);
            unmeta = true;
            unascribe = (uu___116_1088.unascribe)
          }
      | Unascribe  ->
          let uu___117_1089 = fs  in
          {
            beta = (uu___117_1089.beta);
            iota = (uu___117_1089.iota);
            zeta = (uu___117_1089.zeta);
            weak = (uu___117_1089.weak);
            hnf = (uu___117_1089.hnf);
            primops = (uu___117_1089.primops);
            no_delta_steps = (uu___117_1089.no_delta_steps);
            unfold_until = (uu___117_1089.unfold_until);
            unfold_only = (uu___117_1089.unfold_only);
            unfold_attr = (uu___117_1089.unfold_attr);
            unfold_tac = (uu___117_1089.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1089.pure_subterms_within_computations);
            simplify = (uu___117_1089.simplify);
            erase_universes = (uu___117_1089.erase_universes);
            allow_unbound_universes = (uu___117_1089.allow_unbound_universes);
            reify_ = (uu___117_1089.reify_);
            compress_uvars = (uu___117_1089.compress_uvars);
            no_full_norm = (uu___117_1089.no_full_norm);
            check_no_uvars = (uu___117_1089.check_no_uvars);
            unmeta = (uu___117_1089.unmeta);
            unascribe = true
          }
  
let rec (to_fsteps : step Prims.list -> fsteps) =
  fun s  -> FStar_List.fold_right fstep_add_one s default_steps 
type psc =
  {
  psc_range: FStar_Range.range ;
  psc_subst: Prims.unit -> FStar_Syntax_Syntax.subst_t }[@@deriving show]
let (__proj__Mkpsc__item__psc_range : psc -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_range
  
let (__proj__Mkpsc__item__psc_subst :
  psc -> Prims.unit -> FStar_Syntax_Syntax.subst_t) =
  fun projectee  ->
    match projectee with
    | { psc_range = __fname__psc_range; psc_subst = __fname__psc_subst;_} ->
        __fname__psc_subst
  
let (null_psc : psc) =
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1128  -> []) } 
let (psc_range : psc -> FStar_Range.range) = fun psc  -> psc.psc_range 
let (psc_subst : psc -> FStar_Syntax_Syntax.subst_t) =
  fun psc  -> psc.psc_subst () 
type primitive_step =
  {
  name: FStar_Ident.lid ;
  arity: Prims.int ;
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
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__name
  
let (__proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} -> __fname__arity
  
let (__proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
        strong_reduction_ok = __fname__strong_reduction_ok;
        requires_binder_substitution = __fname__requires_binder_substitution;
        interpretation = __fname__interpretation;_} ->
        __fname__strong_reduction_ok
  
let (__proj__Mkprimitive_step__item__requires_binder_substitution :
  primitive_step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { name = __fname__name; arity = __fname__arity;
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
    match projectee with | Clos _0 -> true | uu____1329 -> false
  
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
    match projectee with | Univ _0 -> true | uu____1431 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1442 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
let (closure_to_string : closure -> Prims.string) =
  fun uu___77_1461  ->
    match uu___77_1461 with
    | Clos (uu____1462,t,uu____1464,uu____1465) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____1510 -> "Univ"
    | Dummy  -> "dummy"
  
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
             FStar_Util.psmap_add m1 (FStar_Ident.text_of_lid p.name) p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____1772 = FStar_Util.psmap_empty ()  in add_steps uu____1772 l
  
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
  | Match of (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3
  
  | Abs of
  (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                         FStar_Pervasives_Native.option,
  FStar_Range.range) FStar_Pervasives_Native.tuple5 
  | App of
  (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Meta of (FStar_Syntax_Syntax.metadata,FStar_Range.range)
  FStar_Pervasives_Native.tuple2 
  | Let of
  (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Cfg of cfg 
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____1916 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____1952 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____1988 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2057 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2099 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2155 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2195 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2227 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2263 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2279 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2304 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2304 with | (hd1,uu____2318) -> hd1
  
let (is_embed_position_1 : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2338 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2338 with
    | (hd1,args) ->
        let uu____2369 =
          let uu____2382 =
            let uu____2383 = FStar_Syntax_Util.un_uinst hd1  in
            uu____2383.FStar_Syntax_Syntax.n  in
          (uu____2382, args)  in
        (match uu____2369 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2395::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.fstar_refl_embed_lid
             -> true
         | uu____2422 -> false)
  
let mk :
  'Auu____2438 .
    'Auu____2438 ->
      FStar_Range.range -> 'Auu____2438 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2492 = FStar_ST.op_Bang r  in
          match uu____2492 with
          | FStar_Pervasives_Native.Some uu____2540 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2594 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2594 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___78_2601  ->
    match uu___78_2601 with
    | Arg (c,uu____2603,uu____2604) ->
        let uu____2605 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2605
    | MemoLazy uu____2606 -> "MemoLazy"
    | Abs (uu____2613,bs,uu____2615,uu____2616,uu____2617) ->
        let uu____2622 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2622
    | UnivArgs uu____2627 -> "UnivArgs"
    | Match uu____2634 -> "Match"
    | App (uu____2641,t,uu____2643,uu____2644) ->
        let uu____2645 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2645
    | Meta (m,uu____2647) -> "Meta"
    | Let uu____2648 -> "Let"
    | Cfg uu____2657 -> "Cfg"
    | Debug (t,uu____2659) ->
        let uu____2660 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2660
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2668 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2668 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2699 . 'Auu____2699 Prims.list -> Prims.bool =
  fun uu___79_2705  ->
    match uu___79_2705 with | [] -> true | uu____2708 -> false
  
let lookup_bvar :
  'Auu____2715 'Auu____2716 .
    ('Auu____2716,'Auu____2715) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2715
  =
  fun env  ->
    fun x  ->
      try
        let uu____2740 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____2740
      with
      | uu____2753 ->
          let uu____2754 =
            let uu____2755 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____2755  in
          failwith uu____2754
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    if FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid
      then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
      else
        if FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid
        then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
        else FStar_Pervasives_Native.None
  
let (norm_universe :
  cfg -> env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us
             in
          let uu____2792 =
            FStar_List.fold_left
              (fun uu____2818  ->
                 fun u1  ->
                   match uu____2818 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2843 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2843 with
                        | (k_u,n1) ->
                            let uu____2858 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____2858
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2792 with
          | (uu____2876,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2901 =
                   let uu____2902 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____2902  in
                 match uu____2901 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2920 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2928 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2934 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2943 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2952 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2959 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2959 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2976 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2976 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2984 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2992 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____2992 with
                                  | (uu____2997,m) -> n1 <= m))
                           in
                        if uu____2984 then rest1 else us1
                    | uu____3002 -> us1)
               | uu____3007 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3011 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____3011
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3015 = aux u  in
           match uu____3015 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
  
let rec (closure_as_term :
  cfg -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun cfg  ->
    fun env  ->
      fun t  ->
        log cfg
          (fun uu____3119  ->
             let uu____3120 = FStar_Syntax_Print.tag_of_term t  in
             let uu____3121 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3120
               uu____3121);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3128 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3130 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3155 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3156 -> t1
              | FStar_Syntax_Syntax.Tm_lazy uu____3157 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3158 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3159 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3176 =
                      let uu____3177 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____3178 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3177 uu____3178
                       in
                    failwith uu____3176
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3181 =
                    let uu____3182 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____3182  in
                  mk uu____3181 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3189 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3189
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3191 = lookup_bvar env x  in
                  (match uu____3191 with
                   | Univ uu____3194 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3197,uu____3198) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3310 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3310 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____3338 =
                         let uu____3339 =
                           let uu____3356 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____3356)  in
                         FStar_Syntax_Syntax.Tm_abs uu____3339  in
                       mk uu____3338 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3387 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3387 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3429 =
                    let uu____3440 =
                      let uu____3447 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3447]  in
                    closures_as_binders_delayed cfg env uu____3440  in
                  (match uu____3429 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____3465 =
                         let uu____3466 =
                           let uu____3473 =
                             let uu____3474 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____3474
                               FStar_Pervasives_Native.fst
                              in
                           (uu____3473, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____3466  in
                       mk uu____3465 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3565 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____3565
                    | FStar_Util.Inr c ->
                        let uu____3579 = close_comp cfg env c  in
                        FStar_Util.Inr uu____3579
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____3595 =
                    let uu____3596 =
                      let uu____3623 = closure_as_term_delayed cfg env t11
                         in
                      (uu____3623, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3596  in
                  mk uu____3595 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3674 =
                    let uu____3675 =
                      let uu____3682 = closure_as_term_delayed cfg env t'  in
                      let uu____3685 =
                        let uu____3686 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____3686  in
                      (uu____3682, uu____3685)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3675  in
                  mk uu____3674 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3746 =
                    let uu____3747 =
                      let uu____3754 = closure_as_term_delayed cfg env t'  in
                      let uu____3757 =
                        let uu____3758 =
                          let uu____3765 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____3765)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____3758  in
                      (uu____3754, uu____3757)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3747  in
                  mk uu____3746 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3784 =
                    let uu____3785 =
                      let uu____3792 = closure_as_term_delayed cfg env t'  in
                      let uu____3795 =
                        let uu____3796 =
                          let uu____3805 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____3805)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3796  in
                      (uu____3792, uu____3795)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3785  in
                  mk uu____3784 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_quoted (t'',info)) ->
                  let uu____3823 =
                    let uu____3824 =
                      let uu____3831 = closure_as_term_delayed cfg env t'  in
                      (uu____3831,
                        (FStar_Syntax_Syntax.Meta_quoted (t'', ())))
                       in
                    FStar_Syntax_Syntax.Tm_meta uu____3824  in
                  mk uu____3823 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3844 =
                    let uu____3845 =
                      let uu____3852 = closure_as_term_delayed cfg env t'  in
                      (uu____3852, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3845  in
                  mk uu____3844 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3892  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____3911 =
                    let uu____3922 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____3922
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____3941 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___122_3953 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___122_3953.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___122_3953.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3941))
                     in
                  (match uu____3911 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___123_3969 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___123_3969.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___123_3969.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___123_3969.FStar_Syntax_Syntax.lbattrs)
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3980,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____4039  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____4064 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4064
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____4084  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____4106 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4106
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___124_4118 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_4118.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_4118.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___125_4119 = lb  in
                    let uu____4120 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___125_4119.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___125_4119.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____4120;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___125_4119.FStar_Syntax_Syntax.lbattrs)
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4150  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____4239 =
                    match uu____4239 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4294 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4315 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4375  ->
                                        fun uu____4376  ->
                                          match (uu____4375, uu____4376) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4467 =
                                                norm_pat env3 p1  in
                                              (match uu____4467 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____4315 with
                               | (pats1,env3) ->
                                   ((let uu___126_4549 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___126_4549.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___127_4568 = x  in
                                let uu____4569 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___127_4568.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___127_4568.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4569
                                }  in
                              ((let uu___128_4583 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___128_4583.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___129_4594 = x  in
                                let uu____4595 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___129_4594.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___129_4594.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4595
                                }  in
                              ((let uu___130_4609 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___130_4609.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___131_4625 = x  in
                                let uu____4626 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___131_4625.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___131_4625.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4626
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___132_4633 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___132_4633.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____4636 = norm_pat env1 pat  in
                        (match uu____4636 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4665 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____4665
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____4671 =
                    let uu____4672 =
                      let uu____4695 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____4695)  in
                    FStar_Syntax_Syntax.Tm_match uu____4672  in
                  mk uu____4671 t1.FStar_Syntax_Syntax.pos))

and (closure_as_term_delayed :
  cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> t
        | uu____4781 -> closure_as_term cfg env t

and (closures_as_args_delayed :
  cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
            -> args
        | uu____4807 ->
            FStar_List.map
              (fun uu____4824  ->
                 match uu____4824 with
                 | (x,imp) ->
                     let uu____4843 = closure_as_term_delayed cfg env x  in
                     (uu____4843, imp)) args

and (closures_as_binders_delayed :
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
        let uu____4857 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4906  ->
                  fun uu____4907  ->
                    match (uu____4906, uu____4907) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___133_4977 = b  in
                          let uu____4978 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___133_4977.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___133_4977.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4978
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____4857 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____5071 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5084 = closure_as_term_delayed cfg env t  in
                 let uu____5085 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5084 uu____5085
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5098 = closure_as_term_delayed cfg env t  in
                 let uu____5099 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5098 uu____5099
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   closure_as_term_delayed cfg env
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   closures_as_args_delayed cfg env
                     c1.FStar_Syntax_Syntax.effect_args
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___80_5125  ->
                           match uu___80_5125 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5129 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____5129
                           | f -> f))
                    in
                 let uu____5133 =
                   let uu___134_5134 = c1  in
                   let uu____5135 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5135;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___134_5134.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5133)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___81_5145  ->
            match uu___81_5145 with
            | FStar_Syntax_Syntax.DECREASES uu____5146 -> false
            | uu____5149 -> true))

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
                   (fun uu___82_5167  ->
                      match uu___82_5167 with
                      | FStar_Syntax_Syntax.DECREASES uu____5168 -> false
                      | uu____5171 -> true))
               in
            let rc1 =
              let uu___135_5173 = rc  in
              let uu____5174 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___135_5173.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5174;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5181 -> lopt

let (built_in_primitive_steps : primitive_step FStar_Util.psmap) =
  let arg_as_int a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_int_safe
     in
  let arg_as_bool a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_bool_safe
     in
  let arg_as_char a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_char_safe
     in
  let arg_as_string a =
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      FStar_Syntax_Embeddings.unembed_string_safe
     in
  let arg_as_list a u a =
    let uu____5266 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5266  in
  let arg_as_bounded_int uu____5294 =
    match uu____5294 with
    | (a,uu____5306) ->
        let uu____5313 =
          let uu____5314 = FStar_Syntax_Subst.compress a  in
          uu____5314.FStar_Syntax_Syntax.n  in
        (match uu____5313 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5324;
                FStar_Syntax_Syntax.vars = uu____5325;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5327;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5328;_},uu____5329)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____5368 =
               let uu____5373 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5373)  in
             FStar_Pervasives_Native.Some uu____5368
         | uu____5378 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5418 = f a  in FStar_Pervasives_Native.Some uu____5418
    | uu____5419 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5467 = f a0 a1  in FStar_Pervasives_Native.Some uu____5467
    | uu____5468 -> FStar_Pervasives_Native.None  in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5510 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a415  -> (Obj.magic (f res.psc_range)) a415)
                    uu____5510)) a416 a417 a418 a419 a420
     in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5559 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a421  ->
                       fun a422  -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____5559)) a423 a424 a425 a426 a427
     in
  let as_primitive_step uu____5583 =
    match uu____5583 with
    | (l,arity,f) ->
        {
          name = l;
          arity;
          strong_reduction_ok = true;
          requires_binder_substitution = false;
          interpretation = f
        }
     in
  let unary_int_op f =
    unary_op () (fun a428  -> (Obj.magic arg_as_int) a428)
      (fun a429  ->
         fun a430  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5631 = f x  in
                   FStar_Syntax_Embeddings.embed_int r uu____5631)) a429 a430)
     in
  let binary_int_op f =
    binary_op () (fun a431  -> (Obj.magic arg_as_int) a431)
      (fun a432  ->
         fun a433  ->
           fun a434  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5659 = f x y  in
                       FStar_Syntax_Embeddings.embed_int r uu____5659)) a432
               a433 a434)
     in
  let unary_bool_op f =
    unary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5680 = f x  in
                   FStar_Syntax_Embeddings.embed_bool r uu____5680)) a436
             a437)
     in
  let binary_bool_op f =
    binary_op () (fun a438  -> (Obj.magic arg_as_bool) a438)
      (fun a439  ->
         fun a440  ->
           fun a441  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5708 = f x y  in
                       FStar_Syntax_Embeddings.embed_bool r uu____5708)) a439
               a440 a441)
     in
  let binary_string_op f =
    binary_op () (fun a442  -> (Obj.magic arg_as_string) a442)
      (fun a443  ->
         fun a444  ->
           fun a445  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____5736 = f x y  in
                       FStar_Syntax_Embeddings.embed_string r uu____5736))
               a443 a444 a445)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____5844 =
          let uu____5853 = as_a a  in
          let uu____5856 = as_b b  in (uu____5853, uu____5856)  in
        (match uu____5844 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5871 =
               let uu____5872 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5872  in
             FStar_Pervasives_Native.Some uu____5871
         | uu____5873 -> FStar_Pervasives_Native.None)
    | uu____5882 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____5896 =
        let uu____5897 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5897  in
      mk uu____5896 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5907 =
      let uu____5910 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5910  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5907  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5942 =
      let uu____5943 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5943  in
    FStar_Syntax_Embeddings.embed_int rng uu____5942  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5961 = arg_as_string a1  in
        (match uu____5961 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5967 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2)
                in
             (match uu____5967 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5980 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5980
              | uu____5981 -> FStar_Pervasives_Native.None)
         | uu____5986 -> FStar_Pervasives_Native.None)
    | uu____5989 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5999 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____5999  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r
     in
  let mk_range1 uu____6023 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6034 =
          let uu____6055 = arg_as_string fn  in
          let uu____6058 = arg_as_int from_line  in
          let uu____6061 = arg_as_int from_col  in
          let uu____6064 = arg_as_int to_line  in
          let uu____6067 = arg_as_int to_col  in
          (uu____6055, uu____6058, uu____6061, uu____6064, uu____6067)  in
        (match uu____6034 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6098 =
                 let uu____6099 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6100 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6099 uu____6100  in
               let uu____6101 =
                 let uu____6102 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6103 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6102 uu____6103  in
               FStar_Range.mk_range fn1 uu____6098 uu____6101  in
             let uu____6104 = term_of_range r  in
             FStar_Pervasives_Native.Some uu____6104
         | uu____6109 -> FStar_Pervasives_Native.None)
    | uu____6130 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6157)::(a1,uu____6159)::(a2,uu____6161)::[] ->
        let uu____6198 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6198 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6211 -> FStar_Pervasives_Native.None)
    | uu____6212 -> failwith "Unexpected number of arguments"  in
  let idstep psc args =
    match args with
    | (a1,uu____6239)::[] -> FStar_Pervasives_Native.Some a1
    | uu____6248 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6272 =
      let uu____6287 =
        let uu____6302 =
          let uu____6317 =
            let uu____6332 =
              let uu____6347 =
                let uu____6362 =
                  let uu____6377 =
                    let uu____6392 =
                      let uu____6407 =
                        let uu____6422 =
                          let uu____6437 =
                            let uu____6452 =
                              let uu____6467 =
                                let uu____6482 =
                                  let uu____6497 =
                                    let uu____6512 =
                                      let uu____6527 =
                                        let uu____6542 =
                                          let uu____6557 =
                                            let uu____6572 =
                                              let uu____6587 =
                                                let uu____6600 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____6600,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a446  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a446)
                                                     (fun a447  ->
                                                        fun a448  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a447 a448)))
                                                 in
                                              let uu____6607 =
                                                let uu____6622 =
                                                  let uu____6635 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____6635,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a449  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.unembed_char_safe)))
                                                            a449)
                                                       (fun a450  ->
                                                          fun a451  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a450 a451)))
                                                   in
                                                let uu____6642 =
                                                  let uu____6657 =
                                                    let uu____6672 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____6672,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____6681 =
                                                    let uu____6698 =
                                                      let uu____6713 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____6713,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    let uu____6722 =
                                                      let uu____6739 =
                                                        let uu____6758 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"]
                                                           in
                                                        (uu____6758,
                                                          (Prims.parse_int "1"),
                                                          idstep)
                                                         in
                                                      [uu____6739]  in
                                                    uu____6698 :: uu____6722
                                                     in
                                                  uu____6657 :: uu____6681
                                                   in
                                                uu____6622 :: uu____6642  in
                                              uu____6587 :: uu____6607  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6572
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6557
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a452  ->
                                                (Obj.magic arg_as_string)
                                                  a452)
                                             (fun a453  ->
                                                fun a454  ->
                                                  fun a455  ->
                                                    (Obj.magic
                                                       string_compare') a453
                                                      a454 a455)))
                                          :: uu____6542
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a456  ->
                                              (Obj.magic arg_as_bool) a456)
                                           (fun a457  ->
                                              fun a458  ->
                                                (Obj.magic string_of_bool1)
                                                  a457 a458)))
                                        :: uu____6527
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a459  ->
                                            (Obj.magic arg_as_int) a459)
                                         (fun a460  ->
                                            fun a461  ->
                                              (Obj.magic string_of_int1) a460
                                                a461)))
                                      :: uu____6512
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a462  ->
                                          (Obj.magic arg_as_int) a462)
                                       (fun a463  ->
                                          (Obj.magic arg_as_char) a463)
                                       (fun a464  ->
                                          fun a465  ->
                                            (Obj.magic
                                               FStar_Syntax_Embeddings.embed_string)
                                              a464 a465)
                                       (fun a466  ->
                                          fun a467  ->
                                            fun a468  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____6975 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____6975 y)) a466
                                                a467 a468)))
                                    :: uu____6497
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6482
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6467
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6452
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6437
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6422
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6407
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a469  -> (Obj.magic arg_as_int) a469)
                         (fun a470  ->
                            fun a471  ->
                              fun a472  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____7142 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____7142)) a470 a471 a472)))
                      :: uu____6392
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a473  -> (Obj.magic arg_as_int) a473)
                       (fun a474  ->
                          fun a475  ->
                            fun a476  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____7168 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____7168)) a474 a475 a476)))
                    :: uu____6377
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a477  -> (Obj.magic arg_as_int) a477)
                     (fun a478  ->
                        fun a479  ->
                          fun a480  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____7194 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____7194)) a478 a479 a480)))
                  :: uu____6362
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a481  -> (Obj.magic arg_as_int) a481)
                   (fun a482  ->
                      fun a483  ->
                        fun a484  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____7220 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____7220)) a482 a483 a484)))
                :: uu____6347
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6332
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6317
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6302
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6287
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6272
     in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7373 =
        let uu____7374 =
          let uu____7375 = FStar_Syntax_Syntax.as_arg c  in [uu____7375]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7374  in
      uu____7373 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7425 =
                let uu____7438 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7438, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486  ->
                        fun a487  ->
                          fun a488  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7454  ->
                                    fun uu____7455  ->
                                      match (uu____7454, uu____7455) with
                                      | ((int_to_t1,x),(uu____7474,y)) ->
                                          let uu____7484 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7484)) a486 a487 a488)))
                 in
              let uu____7485 =
                let uu____7500 =
                  let uu____7513 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7513, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490  ->
                          fun a491  ->
                            fun a492  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7529  ->
                                      fun uu____7530  ->
                                        match (uu____7529, uu____7530) with
                                        | ((int_to_t1,x),(uu____7549,y)) ->
                                            let uu____7559 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7559)) a490 a491 a492)))
                   in
                let uu____7560 =
                  let uu____7575 =
                    let uu____7588 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____7588, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494  ->
                            fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7604  ->
                                        fun uu____7605  ->
                                          match (uu____7604, uu____7605) with
                                          | ((int_to_t1,x),(uu____7624,y)) ->
                                              let uu____7634 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____7634)) a494 a495 a496)))
                     in
                  let uu____7635 =
                    let uu____7650 =
                      let uu____7663 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____7663, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498  ->
                              fun a499  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7675  ->
                                        match uu____7675 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499)))
                       in
                    [uu____7650]  in
                  uu____7575 :: uu____7635  in
                uu____7500 :: uu____7560  in
              uu____7425 :: uu____7485))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____7789 =
                let uu____7802 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____7802, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500  -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501  ->
                        fun a502  ->
                          fun a503  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7818  ->
                                    fun uu____7819  ->
                                      match (uu____7818, uu____7819) with
                                      | ((int_to_t1,x),(uu____7838,y)) ->
                                          let uu____7848 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7848)) a501 a502 a503)))
                 in
              let uu____7849 =
                let uu____7864 =
                  let uu____7877 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____7877, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504  -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505  ->
                          fun a506  ->
                            fun a507  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7893  ->
                                      fun uu____7894  ->
                                        match (uu____7893, uu____7894) with
                                        | ((int_to_t1,x),(uu____7913,y)) ->
                                            let uu____7923 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7923)) a505 a506 a507)))
                   in
                [uu____7864]  in
              uu____7789 :: uu____7849))
       in
    FStar_List.append add_sub_mul_v div_mod_unsigned  in
  let uu____7972 =
    FStar_List.map as_primitive_step
      (FStar_List.append basic_ops bounded_arith_ops)
     in
  FStar_All.pipe_left prim_from_list uu____7972 
let (equality_ops : primitive_step FStar_Util.psmap) =
  let interp_prop psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____8020)::(a1,uu____8022)::(a2,uu____8024)::[] ->
        let uu____8061 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8061 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___136_8067 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___136_8067.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___136_8067.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___137_8071 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___137_8071.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___137_8071.FStar_Syntax_Syntax.vars)
                })
         | uu____8072 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8074)::uu____8075::(a1,uu____8077)::(a2,uu____8079)::[] ->
        let uu____8128 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8128 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___136_8134 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___136_8134.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___136_8134.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___137_8138 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___137_8138.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___137_8138.FStar_Syntax_Syntax.vars)
                })
         | uu____8139 -> FStar_Pervasives_Native.None)
    | uu____8140 -> failwith "Unexpected number of arguments"  in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.parse_int "3");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  let hetero_propositional_equality =
    {
      name = FStar_Parser_Const.eq3_lid;
      arity = (Prims.parse_int "4");
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      interpretation = interp_prop
    }  in
  prim_from_list [propositional_equality; hetero_propositional_equality] 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8152 =
      let uu____8153 = FStar_Syntax_Subst.compress t  in
      uu____8153.FStar_Syntax_Syntax.n  in
    match uu____8152 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____8159 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____8159
    | uu____8160 -> FStar_Pervasives_Native.None
  
let mk_psc_subst :
  'Auu____8164 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8164) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8224  ->
           fun subst1  ->
             match uu____8224 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8265,uu____8266)) ->
                      let uu____8325 = b  in
                      (match uu____8325 with
                       | (bv,uu____8333) ->
                           let uu____8334 =
                             let uu____8335 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____8335  in
                           if uu____8334
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8340 = unembed_binder term1  in
                              match uu____8340 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8347 =
                                      let uu___138_8348 = bv  in
                                      let uu____8349 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___138_8348.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___138_8348.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8349
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8347
                                     in
                                  let b_for_x =
                                    let uu____8353 =
                                      let uu____8360 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8360)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8353  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___83_8369  ->
                                         match uu___83_8369 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8370,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8372;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8373;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____8378 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8379 -> subst1)) env []
  
let reduce_primops :
  'Auu____8396 'Auu____8397 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8397) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8396 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8439 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8439 with
             | (head1,args) ->
                 let uu____8476 =
                   let uu____8477 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8477.FStar_Syntax_Syntax.n  in
                 (match uu____8476 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8481 =
                        FStar_Util.psmap_try_find cfg.primitive_steps
                          (FStar_Ident.text_of_lid
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                         in
                      (match uu____8481 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8496  ->
                                   let uu____8497 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____8498 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args)
                                      in
                                   let uu____8505 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8497 uu____8498 uu____8505);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____8510  ->
                                   let uu____8511 =
                                     FStar_Syntax_Print.term_to_string tm  in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____8511);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____8514  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 }  in
                               let uu____8516 =
                                 prim_step.interpretation psc args  in
                               match uu____8516 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____8522  ->
                                         let uu____8523 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____8523);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____8529  ->
                                         let uu____8530 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         let uu____8531 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced
                                            in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____8530 uu____8531);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____8532 ->
                           (log_primops cfg
                              (fun uu____8536  ->
                                 let uu____8537 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8537);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8541  ->
                            let uu____8542 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8542);
                       (match args with
                        | (a1,uu____8544)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8561 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8573  ->
                            let uu____8574 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8574);
                       (match args with
                        | (t,uu____8576)::(r,uu____8578)::[] ->
                            let uu____8605 =
                              FStar_Syntax_Embeddings.unembed_range r  in
                            (match uu____8605 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___139_8609 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___139_8609.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___139_8609.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____8612 -> tm))
                  | uu____8621 -> tm))
  
let reduce_equality :
  'Auu____8626 'Auu____8627 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8627) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8626 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___140_8665 = cfg  in
         {
           steps =
             (let uu___141_8668 = default_steps  in
              {
                beta = (uu___141_8668.beta);
                iota = (uu___141_8668.iota);
                zeta = (uu___141_8668.zeta);
                weak = (uu___141_8668.weak);
                hnf = (uu___141_8668.hnf);
                primops = true;
                no_delta_steps = (uu___141_8668.no_delta_steps);
                unfold_until = (uu___141_8668.unfold_until);
                unfold_only = (uu___141_8668.unfold_only);
                unfold_attr = (uu___141_8668.unfold_attr);
                unfold_tac = (uu___141_8668.unfold_tac);
                pure_subterms_within_computations =
                  (uu___141_8668.pure_subterms_within_computations);
                simplify = (uu___141_8668.simplify);
                erase_universes = (uu___141_8668.erase_universes);
                allow_unbound_universes =
                  (uu___141_8668.allow_unbound_universes);
                reify_ = (uu___141_8668.reify_);
                compress_uvars = (uu___141_8668.compress_uvars);
                no_full_norm = (uu___141_8668.no_full_norm);
                check_no_uvars = (uu___141_8668.check_no_uvars);
                unmeta = (uu___141_8668.unmeta);
                unascribe = (uu___141_8668.unascribe)
              });
           tcenv = (uu___140_8665.tcenv);
           debug = (uu___140_8665.debug);
           delta_level = (uu___140_8665.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___140_8665.strong);
           memoize_lazy = (uu___140_8665.memoize_lazy);
           normalize_pure_lets = (uu___140_8665.normalize_pure_lets)
         }) tm
  
let maybe_simplify_aux :
  'Auu____8675 'Auu____8676 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8676) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8675 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____8718 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____8718
          then tm1
          else
            (let w t =
               let uu___142_8730 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___142_8730.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___142_8730.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____8746;
                      FStar_Syntax_Syntax.vars = uu____8747;_},uu____8748)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____8755;
                      FStar_Syntax_Syntax.vars = uu____8756;_},uu____8757)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____8763 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____8768 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____8768
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____8789 =
                 match uu____8789 with
                 | (t1,q) ->
                     let uu____8802 = FStar_Syntax_Util.is_auto_squash t1  in
                     (match uu____8802 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____8830 -> (t1, q))
                  in
               let uu____8839 = FStar_Syntax_Util.head_and_args t  in
               match uu____8839 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let simplify1 arg =
               ((simp_t (FStar_Pervasives_Native.fst arg)), arg)  in
             match tm1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____8936;
                         FStar_Syntax_Syntax.vars = uu____8937;_},uu____8938);
                    FStar_Syntax_Syntax.pos = uu____8939;
                    FStar_Syntax_Syntax.vars = uu____8940;_},args)
                 ->
                 let uu____8966 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____8966
                 then
                   let uu____8967 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____8967 with
                    | (FStar_Pervasives_Native.Some (true ),uu____9022)::
                        (uu____9023,(arg,uu____9025))::[] ->
                        maybe_auto_squash arg
                    | (uu____9090,(arg,uu____9092))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9093)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9158)::uu____9159::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9222::(FStar_Pervasives_Native.Some (false
                                   ),uu____9223)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9286 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9302 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____9302
                    then
                      let uu____9303 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____9303 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9358)::uu____9359::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9422::(FStar_Pervasives_Native.Some (true
                                     ),uu____9423)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9486)::
                          (uu____9487,(arg,uu____9489))::[] ->
                          maybe_auto_squash arg
                      | (uu____9554,(arg,uu____9556))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9557)::[]
                          -> maybe_auto_squash arg
                      | uu____9622 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9638 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____9638
                       then
                         let uu____9639 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____9639 with
                         | uu____9694::(FStar_Pervasives_Native.Some (true
                                        ),uu____9695)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9758)::uu____9759::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9822)::
                             (uu____9823,(arg,uu____9825))::[] ->
                             maybe_auto_squash arg
                         | (uu____9890,(p,uu____9892))::(uu____9893,(q,uu____9895))::[]
                             ->
                             let uu____9960 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____9960
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9962 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9978 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.iff_lid
                             in
                          if uu____9978
                          then
                            let uu____9979 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____9979 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10034)::(FStar_Pervasives_Native.Some
                                                (true ),uu____10035)::[]
                                -> w FStar_Syntax_Util.t_true
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10100)::(FStar_Pervasives_Native.Some
                                                (false ),uu____10101)::[]
                                -> w FStar_Syntax_Util.t_true
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10166)::(FStar_Pervasives_Native.Some
                                                (false ),uu____10167)::[]
                                -> w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10232)::(FStar_Pervasives_Native.Some
                                                (true ),uu____10233)::[]
                                -> w FStar_Syntax_Util.t_false
                            | (uu____10298,(arg,uu____10300))::(FStar_Pervasives_Native.Some
                                                                (true
                                                                ),uu____10301)::[]
                                -> maybe_auto_squash arg
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10366)::(uu____10367,(arg,uu____10369))::[]
                                -> maybe_auto_squash arg
                            | (uu____10434,(p,uu____10436))::(uu____10437,
                                                              (q,uu____10439))::[]
                                ->
                                let uu____10504 =
                                  FStar_Syntax_Util.term_eq p q  in
                                (if uu____10504
                                 then w FStar_Syntax_Util.t_true
                                 else squashed_head_un_auto_squash_args tm1)
                            | uu____10506 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10522 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.not_lid
                                in
                             if uu____10522
                             then
                               let uu____10523 =
                                 FStar_All.pipe_right args
                                   (FStar_List.map simplify1)
                                  in
                               match uu____10523 with
                               | (FStar_Pervasives_Native.Some (true
                                  ),uu____10578)::[] ->
                                   w FStar_Syntax_Util.t_false
                               | (FStar_Pervasives_Native.Some (false
                                  ),uu____10617)::[] ->
                                   w FStar_Syntax_Util.t_true
                               | uu____10656 ->
                                   squashed_head_un_auto_squash_args tm1
                             else
                               (let uu____10672 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.forall_lid
                                   in
                                if uu____10672
                                then
                                  match args with
                                  | (t,uu____10674)::[] ->
                                      let uu____10691 =
                                        let uu____10692 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10692.FStar_Syntax_Syntax.n  in
                                      (match uu____10691 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10695::[],body,uu____10697)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (true ) ->
                                                w FStar_Syntax_Util.t_true
                                            | uu____10724 -> tm1)
                                       | uu____10727 -> tm1)
                                  | (uu____10728,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10729))::(t,uu____10731)::[] ->
                                      let uu____10770 =
                                        let uu____10771 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10771.FStar_Syntax_Syntax.n  in
                                      (match uu____10770 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10774::[],body,uu____10776)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (true ) ->
                                                w FStar_Syntax_Util.t_true
                                            | uu____10803 -> tm1)
                                       | uu____10806 -> tm1)
                                  | uu____10807 -> tm1
                                else
                                  (let uu____10817 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.exists_lid
                                      in
                                   if uu____10817
                                   then
                                     match args with
                                     | (t,uu____10819)::[] ->
                                         let uu____10836 =
                                           let uu____10837 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____10837.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____10836 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (uu____10840::[],body,uu____10842)
                                              ->
                                              (match simp_t body with
                                               | FStar_Pervasives_Native.Some
                                                   (false ) ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____10869 -> tm1)
                                          | uu____10872 -> tm1)
                                     | (uu____10873,FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit
                                        uu____10874))::(t,uu____10876)::[] ->
                                         let uu____10915 =
                                           let uu____10916 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____10916.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____10915 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (uu____10919::[],body,uu____10921)
                                              ->
                                              (match simp_t body with
                                               | FStar_Pervasives_Native.Some
                                                   (false ) ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____10948 -> tm1)
                                          | uu____10951 -> tm1)
                                     | uu____10952 -> tm1
                                   else
                                     (let uu____10962 =
                                        FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.b2t_lid
                                         in
                                      if uu____10962
                                      then
                                        match args with
                                        | ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_constant
                                               (FStar_Const.Const_bool (true
                                               ));
                                             FStar_Syntax_Syntax.pos =
                                               uu____10963;
                                             FStar_Syntax_Syntax.vars =
                                               uu____10964;_},uu____10965)::[]
                                            -> w FStar_Syntax_Util.t_true
                                        | ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_constant
                                               (FStar_Const.Const_bool (false
                                               ));
                                             FStar_Syntax_Syntax.pos =
                                               uu____10982;
                                             FStar_Syntax_Syntax.vars =
                                               uu____10983;_},uu____10984)::[]
                                            -> w FStar_Syntax_Util.t_false
                                        | uu____11001 -> tm1
                                      else
                                        (let uu____11011 =
                                           FStar_Syntax_Util.is_auto_squash
                                             tm1
                                            in
                                         match uu____11011 with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.U_zero ,t)
                                             when
                                             FStar_Syntax_Util.is_sub_singleton
                                               t
                                             -> t
                                         | uu____11031 ->
                                             reduce_equality cfg env stack
                                               tm1))))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____11041;
                    FStar_Syntax_Syntax.vars = uu____11042;_},args)
                 ->
                 let uu____11064 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____11064
                 then
                   let uu____11065 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____11065 with
                    | (FStar_Pervasives_Native.Some (true ),uu____11120)::
                        (uu____11121,(arg,uu____11123))::[] ->
                        maybe_auto_squash arg
                    | (uu____11188,(arg,uu____11190))::(FStar_Pervasives_Native.Some
                                                        (true ),uu____11191)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____11256)::uu____11257::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____11320::(FStar_Pervasives_Native.Some (false
                                    ),uu____11321)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____11384 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____11400 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____11400
                    then
                      let uu____11401 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____11401 with
                      | (FStar_Pervasives_Native.Some (true ),uu____11456)::uu____11457::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____11520::(FStar_Pervasives_Native.Some (true
                                      ),uu____11521)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____11584)::
                          (uu____11585,(arg,uu____11587))::[] ->
                          maybe_auto_squash arg
                      | (uu____11652,(arg,uu____11654))::(FStar_Pervasives_Native.Some
                                                          (false
                                                          ),uu____11655)::[]
                          -> maybe_auto_squash arg
                      | uu____11720 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____11736 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____11736
                       then
                         let uu____11737 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____11737 with
                         | uu____11792::(FStar_Pervasives_Native.Some (true
                                         ),uu____11793)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____11856)::uu____11857::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____11920)::
                             (uu____11921,(arg,uu____11923))::[] ->
                             maybe_auto_squash arg
                         | (uu____11988,(p,uu____11990))::(uu____11991,
                                                           (q,uu____11993))::[]
                             ->
                             let uu____12058 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____12058
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____12060 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____12076 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.iff_lid
                             in
                          if uu____12076
                          then
                            let uu____12077 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____12077 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____12132)::(FStar_Pervasives_Native.Some
                                                (true ),uu____12133)::[]
                                -> w FStar_Syntax_Util.t_true
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____12198)::(FStar_Pervasives_Native.Some
                                                (false ),uu____12199)::[]
                                -> w FStar_Syntax_Util.t_true
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____12264)::(FStar_Pervasives_Native.Some
                                                (false ),uu____12265)::[]
                                -> w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____12330)::(FStar_Pervasives_Native.Some
                                                (true ),uu____12331)::[]
                                -> w FStar_Syntax_Util.t_false
                            | (uu____12396,(arg,uu____12398))::(FStar_Pervasives_Native.Some
                                                                (true
                                                                ),uu____12399)::[]
                                -> maybe_auto_squash arg
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____12464)::(uu____12465,(arg,uu____12467))::[]
                                -> maybe_auto_squash arg
                            | (uu____12532,(p,uu____12534))::(uu____12535,
                                                              (q,uu____12537))::[]
                                ->
                                let uu____12602 =
                                  FStar_Syntax_Util.term_eq p q  in
                                (if uu____12602
                                 then w FStar_Syntax_Util.t_true
                                 else squashed_head_un_auto_squash_args tm1)
                            | uu____12604 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____12620 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.not_lid
                                in
                             if uu____12620
                             then
                               let uu____12621 =
                                 FStar_All.pipe_right args
                                   (FStar_List.map simplify1)
                                  in
                               match uu____12621 with
                               | (FStar_Pervasives_Native.Some (true
                                  ),uu____12676)::[] ->
                                   w FStar_Syntax_Util.t_false
                               | (FStar_Pervasives_Native.Some (false
                                  ),uu____12715)::[] ->
                                   w FStar_Syntax_Util.t_true
                               | uu____12754 ->
                                   squashed_head_un_auto_squash_args tm1
                             else
                               (let uu____12770 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.forall_lid
                                   in
                                if uu____12770
                                then
                                  match args with
                                  | (t,uu____12772)::[] ->
                                      let uu____12789 =
                                        let uu____12790 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____12790.FStar_Syntax_Syntax.n  in
                                      (match uu____12789 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____12793::[],body,uu____12795)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (true ) ->
                                                w FStar_Syntax_Util.t_true
                                            | uu____12822 -> tm1)
                                       | uu____12825 -> tm1)
                                  | (uu____12826,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____12827))::(t,uu____12829)::[] ->
                                      let uu____12868 =
                                        let uu____12869 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____12869.FStar_Syntax_Syntax.n  in
                                      (match uu____12868 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____12872::[],body,uu____12874)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (true ) ->
                                                w FStar_Syntax_Util.t_true
                                            | uu____12901 -> tm1)
                                       | uu____12904 -> tm1)
                                  | uu____12905 -> tm1
                                else
                                  (let uu____12915 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.exists_lid
                                      in
                                   if uu____12915
                                   then
                                     match args with
                                     | (t,uu____12917)::[] ->
                                         let uu____12934 =
                                           let uu____12935 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____12935.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____12934 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (uu____12938::[],body,uu____12940)
                                              ->
                                              (match simp_t body with
                                               | FStar_Pervasives_Native.Some
                                                   (false ) ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____12967 -> tm1)
                                          | uu____12970 -> tm1)
                                     | (uu____12971,FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit
                                        uu____12972))::(t,uu____12974)::[] ->
                                         let uu____13013 =
                                           let uu____13014 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____13014.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____13013 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (uu____13017::[],body,uu____13019)
                                              ->
                                              (match simp_t body with
                                               | FStar_Pervasives_Native.Some
                                                   (false ) ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____13046 -> tm1)
                                          | uu____13049 -> tm1)
                                     | uu____13050 -> tm1
                                   else
                                     (let uu____13060 =
                                        FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.b2t_lid
                                         in
                                      if uu____13060
                                      then
                                        match args with
                                        | ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_constant
                                               (FStar_Const.Const_bool (true
                                               ));
                                             FStar_Syntax_Syntax.pos =
                                               uu____13061;
                                             FStar_Syntax_Syntax.vars =
                                               uu____13062;_},uu____13063)::[]
                                            -> w FStar_Syntax_Util.t_true
                                        | ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_constant
                                               (FStar_Const.Const_bool (false
                                               ));
                                             FStar_Syntax_Syntax.pos =
                                               uu____13080;
                                             FStar_Syntax_Syntax.vars =
                                               uu____13081;_},uu____13082)::[]
                                            -> w FStar_Syntax_Util.t_false
                                        | uu____13099 -> tm1
                                      else
                                        (let uu____13109 =
                                           FStar_Syntax_Util.is_auto_squash
                                             tm1
                                            in
                                         match uu____13109 with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.U_zero ,t)
                                             when
                                             FStar_Syntax_Util.is_sub_singleton
                                               t
                                             -> t
                                         | uu____13129 ->
                                             reduce_equality cfg env stack
                                               tm1))))))))
             | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                 (match simp_t t with
                  | FStar_Pervasives_Native.Some (true ) ->
                      bv.FStar_Syntax_Syntax.sort
                  | FStar_Pervasives_Native.Some (false ) -> tm1
                  | FStar_Pervasives_Native.None  -> tm1)
             | uu____13144 -> tm1)
  
let maybe_simplify :
  'Auu____13151 'Auu____13152 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____13152) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____13151 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.debug).b380
          then
            (let uu____13195 = FStar_Syntax_Print.term_to_string tm  in
             let uu____13196 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____13195
               uu____13196)
          else ();
          tm'
  
let is_norm_request :
  'Auu____13202 .
    FStar_Syntax_Syntax.term -> 'Auu____13202 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____13215 =
        let uu____13222 =
          let uu____13223 = FStar_Syntax_Util.un_uinst hd1  in
          uu____13223.FStar_Syntax_Syntax.n  in
        (uu____13222, args)  in
      match uu____13215 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____13229::uu____13230::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____13234::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____13239::uu____13240::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____13243 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___84_13254  ->
    match uu___84_13254 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____13260 =
          let uu____13263 =
            let uu____13264 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____13264  in
          [uu____13263]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____13260
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____13280 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____13280) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        try
          let uu____13333 =
            let uu____13336 =
              let uu____13339 =
                let uu____13344 =
                  FStar_Syntax_Embeddings.unembed_list_safe
                    FStar_Syntax_Embeddings.unembed_norm_step
                   in
                uu____13344 s  in
              FStar_All.pipe_right uu____13339 FStar_Util.must  in
            FStar_All.pipe_right uu____13336 tr_norm_steps  in
          FStar_Pervasives_Native.Some uu____13333
        with | uu____13372 -> FStar_Pervasives_Native.None  in
      match args with
      | uu____13383::(tm,uu____13385)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____13414)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____13435)::uu____13436::(tm,uu____13438)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____13475 =
            let uu____13480 = full_norm steps  in parse_steps uu____13480  in
          (match uu____13475 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____13519 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___85_13536  ->
    match uu___85_13536 with
    | (App
        (uu____13539,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____13540;
                       FStar_Syntax_Syntax.vars = uu____13541;_},uu____13542,uu____13543))::uu____13544
        -> true
    | uu____13551 -> false
  
let firstn :
  'Auu____13557 .
    Prims.int ->
      'Auu____13557 Prims.list ->
        ('Auu____13557 Prims.list,'Auu____13557 Prims.list)
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
          (uu____13593,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____13594;
                         FStar_Syntax_Syntax.vars = uu____13595;_},uu____13596,uu____13597))::uu____13598
          -> (cfg.steps).reify_
      | uu____13605 -> false
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let r =
        let uu____13615 = FStar_Syntax_Util.eq_tm a a'  in
        match uu____13615 with
        | FStar_Syntax_Util.Equal  -> true
        | uu____13616 -> false  in
      r
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____13758 ->
                   let uu____13783 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____13783
               | uu____13784 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____13792  ->
               let uu____13793 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____13794 = FStar_Syntax_Print.term_to_string t1  in
               let uu____13795 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____13802 =
                 let uu____13803 =
                   let uu____13806 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____13806
                    in
                 stack_to_string uu____13803  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____13793 uu____13794 uu____13795 uu____13802);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____13829 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____13830 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____13831 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13832;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____13833;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13836;
                 FStar_Syntax_Syntax.fv_delta = uu____13837;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13838;
                 FStar_Syntax_Syntax.fv_delta = uu____13839;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____13840);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_meta
               (t0,FStar_Syntax_Syntax.Meta_quoted (t11,inf)) ->
               let t01 = closure_as_term cfg env t0  in
               let t2 =
                 let uu___145_13862 = t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_meta
                        (t01, (FStar_Syntax_Syntax.Meta_quoted (t11, ()))));
                   FStar_Syntax_Syntax.pos =
                     (uu___145_13862.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___145_13862.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack t2
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (Prims.op_Negation
                    (FStar_Ident.lid_equals
                       (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                       FStar_Parser_Const.prims_lid))
               ->
               let cfg' =
                 let uu___146_13894 = cfg  in
                 {
                   steps =
                     (let uu___147_13897 = cfg.steps  in
                      {
                        beta = (uu___147_13897.beta);
                        iota = (uu___147_13897.iota);
                        zeta = (uu___147_13897.zeta);
                        weak = (uu___147_13897.weak);
                        hnf = (uu___147_13897.hnf);
                        primops = (uu___147_13897.primops);
                        no_delta_steps = false;
                        unfold_until = (uu___147_13897.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___147_13897.unfold_attr);
                        unfold_tac = (uu___147_13897.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___147_13897.pure_subterms_within_computations);
                        simplify = (uu___147_13897.simplify);
                        erase_universes = (uu___147_13897.erase_universes);
                        allow_unbound_universes =
                          (uu___147_13897.allow_unbound_universes);
                        reify_ = (uu___147_13897.reify_);
                        compress_uvars = (uu___147_13897.compress_uvars);
                        no_full_norm = (uu___147_13897.no_full_norm);
                        check_no_uvars = (uu___147_13897.check_no_uvars);
                        unmeta = (uu___147_13897.unmeta);
                        unascribe = (uu___147_13897.unascribe)
                      });
                   tcenv = (uu___146_13894.tcenv);
                   debug = (uu___146_13894.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___146_13894.primitive_steps);
                   strong = (uu___146_13894.strong);
                   memoize_lazy = (uu___146_13894.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____13900 = get_norm_request (norm cfg' env []) args  in
               (match uu____13900 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____13931  ->
                              fun stack1  ->
                                match uu____13931 with
                                | (a,aq) ->
                                    let uu____13943 =
                                      let uu____13944 =
                                        let uu____13951 =
                                          let uu____13952 =
                                            let uu____13983 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____13983, false)  in
                                          Clos uu____13952  in
                                        (uu____13951, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____13944  in
                                    uu____13943 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____14067  ->
                          let uu____14068 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____14068);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____14090 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___86_14095  ->
                                match uu___86_14095 with
                                | UnfoldUntil uu____14096 -> true
                                | UnfoldOnly uu____14097 -> true
                                | uu____14100 -> false))
                         in
                      if uu____14090
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___148_14105 = cfg  in
                      let uu____14106 = to_fsteps s  in
                      {
                        steps = uu____14106;
                        tcenv = (uu___148_14105.tcenv);
                        debug = (uu___148_14105.debug);
                        delta_level;
                        primitive_steps = (uu___148_14105.primitive_steps);
                        strong = (uu___148_14105.strong);
                        memoize_lazy = (uu___148_14105.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____14115 =
                          let uu____14116 =
                            let uu____14121 = FStar_Util.now ()  in
                            (t1, uu____14121)  in
                          Debug uu____14116  in
                        uu____14115 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____14125 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14125
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____14134 =
                      let uu____14141 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____14141, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____14134  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____14151 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____14151  in
               let uu____14152 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____14152
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____14158  ->
                       let uu____14159 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____14160 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____14159 uu____14160);
                  if b
                  then
                    (let uu____14161 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____14161 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    FStar_All.pipe_right cfg.delta_level
                      (FStar_Util.for_some
                         (fun uu___87_14170  ->
                            match uu___87_14170 with
                            | FStar_TypeChecker_Env.UnfoldTac  -> false
                            | FStar_TypeChecker_Env.NoDelta  -> false
                            | FStar_TypeChecker_Env.Inlining  -> true
                            | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                                true
                            | FStar_TypeChecker_Env.Unfold l ->
                                FStar_TypeChecker_Common.delta_depth_greater_than
                                  fv.FStar_Syntax_Syntax.fv_delta l))
                     in
                  let should_delta1 =
                    should_delta &&
                      (let attrs =
                         FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
                       ((Prims.op_Negation (cfg.steps).unfold_tac) ||
                          (let uu____14180 =
                             cases
                               (FStar_Util.for_some
                                  (attr_eq FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____14180))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____14199) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some (attr_eq at) ats')
                                   ats
                             | (uu____14234,uu____14235) -> false)))
                     in
                  log cfg
                    (fun uu____14257  ->
                       let uu____14258 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____14259 =
                         FStar_Range.string_of_range
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14260 =
                         FStar_Util.string_of_bool should_delta1  in
                       FStar_Util.print3
                         ">>> For %s (%s), should_delta = %s\n" uu____14258
                         uu____14259 uu____14260);
                  if should_delta1
                  then do_unfold_fv cfg env stack t1 qninfo fv
                  else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____14263 = lookup_bvar env x  in
               (match uu____14263 with
                | Univ uu____14266 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____14315 = FStar_ST.op_Bang r  in
                      (match uu____14315 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____14433  ->
                                 let uu____14434 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____14435 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____14434
                                   uu____14435);
                            (let uu____14436 =
                               let uu____14437 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____14437.FStar_Syntax_Syntax.n  in
                             match uu____14436 with
                             | FStar_Syntax_Syntax.Tm_abs uu____14440 ->
                                 norm cfg env2 stack t'
                             | uu____14457 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____14527)::uu____14528 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____14537)::uu____14538 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____14548,uu____14549))::stack_rest ->
                    (match c with
                     | Univ uu____14553 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____14562 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____14583  ->
                                    let uu____14584 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14584);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____14624  ->
                                    let uu____14625 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14625);
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
                       (fun uu____14703  ->
                          let uu____14704 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____14704);
                     norm cfg env stack1 t1)
                | (Debug uu____14705)::uu____14706 ->
                    if (cfg.steps).weak
                    then
                      let uu____14713 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14713
                    else
                      (let uu____14715 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14715 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14757  -> dummy :: env1) env)
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
                                          let uu____14794 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14794)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_14799 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_14799.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_14799.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14800 -> lopt  in
                           (log cfg
                              (fun uu____14806  ->
                                 let uu____14807 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14807);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_14816 = cfg  in
                               {
                                 steps = (uu___150_14816.steps);
                                 tcenv = (uu___150_14816.tcenv);
                                 debug = (uu___150_14816.debug);
                                 delta_level = (uu___150_14816.delta_level);
                                 primitive_steps =
                                   (uu___150_14816.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_14816.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_14816.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____14827)::uu____14828 ->
                    if (cfg.steps).weak
                    then
                      let uu____14835 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14835
                    else
                      (let uu____14837 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14837 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14879  -> dummy :: env1) env)
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
                                          let uu____14916 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14916)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_14921 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_14921.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_14921.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14922 -> lopt  in
                           (log cfg
                              (fun uu____14928  ->
                                 let uu____14929 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14929);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_14938 = cfg  in
                               {
                                 steps = (uu___150_14938.steps);
                                 tcenv = (uu___150_14938.tcenv);
                                 debug = (uu___150_14938.debug);
                                 delta_level = (uu___150_14938.delta_level);
                                 primitive_steps =
                                   (uu___150_14938.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_14938.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_14938.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____14949)::uu____14950 ->
                    if (cfg.steps).weak
                    then
                      let uu____14961 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14961
                    else
                      (let uu____14963 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14963 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15005  -> dummy :: env1) env)
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
                                          let uu____15042 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15042)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_15047 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_15047.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_15047.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15048 -> lopt  in
                           (log cfg
                              (fun uu____15054  ->
                                 let uu____15055 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15055);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_15064 = cfg  in
                               {
                                 steps = (uu___150_15064.steps);
                                 tcenv = (uu___150_15064.tcenv);
                                 debug = (uu___150_15064.debug);
                                 delta_level = (uu___150_15064.delta_level);
                                 primitive_steps =
                                   (uu___150_15064.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_15064.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_15064.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____15075)::uu____15076 ->
                    if (cfg.steps).weak
                    then
                      let uu____15087 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15087
                    else
                      (let uu____15089 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15089 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15131  -> dummy :: env1) env)
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
                                          let uu____15168 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15168)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_15173 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_15173.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_15173.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15174 -> lopt  in
                           (log cfg
                              (fun uu____15180  ->
                                 let uu____15181 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15181);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_15190 = cfg  in
                               {
                                 steps = (uu___150_15190.steps);
                                 tcenv = (uu___150_15190.tcenv);
                                 debug = (uu___150_15190.debug);
                                 delta_level = (uu___150_15190.delta_level);
                                 primitive_steps =
                                   (uu___150_15190.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_15190.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_15190.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____15201)::uu____15202 ->
                    if (cfg.steps).weak
                    then
                      let uu____15217 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15217
                    else
                      (let uu____15219 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15219 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15261  -> dummy :: env1) env)
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
                                          let uu____15298 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15298)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_15303 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_15303.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_15303.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15304 -> lopt  in
                           (log cfg
                              (fun uu____15310  ->
                                 let uu____15311 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15311);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_15320 = cfg  in
                               {
                                 steps = (uu___150_15320.steps);
                                 tcenv = (uu___150_15320.tcenv);
                                 debug = (uu___150_15320.debug);
                                 delta_level = (uu___150_15320.delta_level);
                                 primitive_steps =
                                   (uu___150_15320.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_15320.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_15320.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____15331 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15331
                    else
                      (let uu____15333 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15333 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15375  -> dummy :: env1) env)
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
                                          let uu____15412 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15412)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_15417 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_15417.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_15417.FStar_Syntax_Syntax.residual_flags)
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
                               let uu___150_15434 = cfg  in
                               {
                                 steps = (uu___150_15434.steps);
                                 tcenv = (uu___150_15434.tcenv);
                                 debug = (uu___150_15434.debug);
                                 delta_level = (uu___150_15434.delta_level);
                                 primitive_steps =
                                   (uu___150_15434.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_15434.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_15434.normalize_pure_lets)
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
                      (fun uu____15483  ->
                         fun stack1  ->
                           match uu____15483 with
                           | (a,aq) ->
                               let uu____15495 =
                                 let uu____15496 =
                                   let uu____15503 =
                                     let uu____15504 =
                                       let uu____15535 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____15535, false)  in
                                     Clos uu____15504  in
                                   (uu____15503, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____15496  in
                               uu____15495 :: stack1) args)
                  in
               (log cfg
                  (fun uu____15619  ->
                     let uu____15620 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____15620);
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
                             ((let uu___151_15656 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___151_15656.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___151_15656.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____15657 ->
                      let uu____15662 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15662)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____15665 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____15665 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____15696 =
                          let uu____15697 =
                            let uu____15704 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___152_15706 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___152_15706.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___152_15706.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____15704)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____15697  in
                        mk uu____15696 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____15725 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____15725
               else
                 (let uu____15727 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____15727 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____15735 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____15759  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____15735 c1  in
                      let t2 =
                        let uu____15781 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____15781 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____15892)::uu____15893 ->
                    (log cfg
                       (fun uu____15904  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____15905)::uu____15906 ->
                    (log cfg
                       (fun uu____15917  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____15918,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____15919;
                                   FStar_Syntax_Syntax.vars = uu____15920;_},uu____15921,uu____15922))::uu____15923
                    ->
                    (log cfg
                       (fun uu____15932  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____15933)::uu____15934 ->
                    (log cfg
                       (fun uu____15945  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____15946 ->
                    (log cfg
                       (fun uu____15949  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____15953  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____15970 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____15970
                         | FStar_Util.Inr c ->
                             let uu____15978 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____15978
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____15991 =
                               let uu____15992 =
                                 let uu____16019 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16019, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____15992
                                in
                             mk uu____15991 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____16038 ->
                           let uu____16039 =
                             let uu____16040 =
                               let uu____16041 =
                                 let uu____16068 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____16068, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____16041
                                in
                             mk uu____16040 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____16039))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, (t1.FStar_Syntax_Syntax.pos))) ::
                 stack  in
               norm cfg env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.steps).compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____16178 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____16178 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___153_16198 = cfg  in
                               let uu____16199 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___153_16198.steps);
                                 tcenv = uu____16199;
                                 debug = (uu___153_16198.debug);
                                 delta_level = (uu___153_16198.delta_level);
                                 primitive_steps =
                                   (uu___153_16198.primitive_steps);
                                 strong = (uu___153_16198.strong);
                                 memoize_lazy = (uu___153_16198.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___153_16198.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____16204 =
                                 let uu____16205 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____16205  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____16204
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___154_16208 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___154_16208.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___154_16208.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___154_16208.FStar_Syntax_Syntax.lbattrs)
                             }))
                  in
               let uu____16209 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____16209
           | FStar_Syntax_Syntax.Tm_let
               ((uu____16220,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____16221;
                               FStar_Syntax_Syntax.lbunivs = uu____16222;
                               FStar_Syntax_Syntax.lbtyp = uu____16223;
                               FStar_Syntax_Syntax.lbeff = uu____16224;
                               FStar_Syntax_Syntax.lbdef = uu____16225;
                               FStar_Syntax_Syntax.lbattrs = uu____16226;_}::uu____16227),uu____16228)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____16268 =
                 (Prims.op_Negation (cfg.steps).no_delta_steps) &&
                   ((((cfg.steps).pure_subterms_within_computations &&
                        (FStar_Util.for_some
                           (FStar_Syntax_Util.is_fvar
                              FStar_Parser_Const.inline_let_attr)
                           lb.FStar_Syntax_Syntax.lbattrs))
                       ||
                       ((FStar_Syntax_Util.is_pure_effect n1) &&
                          (cfg.normalize_pure_lets ||
                             (FStar_Util.for_some
                                (FStar_Syntax_Util.is_fvar
                                   FStar_Parser_Const.inline_let_attr)
                                lb.FStar_Syntax_Syntax.lbattrs))))
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (Prims.op_Negation
                            (cfg.steps).pure_subterms_within_computations)))
                  in
               if uu____16268
               then
                 let binder =
                   let uu____16270 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____16270  in
                 let env1 =
                   let uu____16280 =
                     let uu____16287 =
                       let uu____16288 =
                         let uu____16319 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____16319,
                           false)
                          in
                       Clos uu____16288  in
                     ((FStar_Pervasives_Native.Some binder), uu____16287)  in
                   uu____16280 :: env  in
                 (log cfg
                    (fun uu____16412  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____16416  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____16417 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____16417))
                 else
                   (let uu____16419 =
                      let uu____16424 =
                        let uu____16425 =
                          let uu____16426 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____16426
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____16425]  in
                      FStar_Syntax_Subst.open_term uu____16424 body  in
                    match uu____16419 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____16435  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____16443 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____16443  in
                            FStar_Util.Inl
                              (let uu___155_16453 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___155_16453.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___155_16453.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____16456  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___156_16458 = lb  in
                             let uu____16459 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___156_16458.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___156_16458.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16459;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___156_16458.FStar_Syntax_Syntax.lbattrs)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16494  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___157_16517 = cfg  in
                             {
                               steps = (uu___157_16517.steps);
                               tcenv = (uu___157_16517.tcenv);
                               debug = (uu___157_16517.debug);
                               delta_level = (uu___157_16517.delta_level);
                               primitive_steps =
                                 (uu___157_16517.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___157_16517.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___157_16517.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____16520  ->
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
               let uu____16537 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____16537 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____16573 =
                               let uu___158_16574 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___158_16574.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___158_16574.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____16573  in
                           let uu____16575 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____16575 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____16601 =
                                   FStar_List.map (fun uu____16617  -> dummy)
                                     lbs1
                                    in
                                 let uu____16618 =
                                   let uu____16627 =
                                     FStar_List.map
                                       (fun uu____16647  -> dummy) xs1
                                      in
                                   FStar_List.append uu____16627 env  in
                                 FStar_List.append uu____16601 uu____16618
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____16671 =
                                       let uu___159_16672 = rc  in
                                       let uu____16673 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___159_16672.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____16673;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___159_16672.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____16671
                                 | uu____16680 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___160_16684 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___160_16684.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___160_16684.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___160_16684.FStar_Syntax_Syntax.lbattrs)
                               }) lbs1
                       in
                    let env' =
                      let uu____16694 =
                        FStar_List.map (fun uu____16710  -> dummy) lbs2  in
                      FStar_List.append uu____16694 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____16718 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____16718 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___161_16734 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___161_16734.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___161_16734.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____16761 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____16761
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____16780 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____16856  ->
                        match uu____16856 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___162_16977 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___162_16977.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___162_16977.FStar_Syntax_Syntax.sort)
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
               (match uu____16780 with
                | (rec_env,memos,uu____17190) ->
                    let uu____17243 =
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
                             let uu____17554 =
                               let uu____17561 =
                                 let uu____17562 =
                                   let uu____17593 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____17593, false)
                                    in
                                 Clos uu____17562  in
                               (FStar_Pervasives_Native.None, uu____17561)
                                in
                             uu____17554 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____17703  ->
                     let uu____17704 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____17704);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | FStar_Syntax_Syntax.Meta_quoted (qt,inf) ->
                     rebuild cfg env stack t1
                 | uu____17732 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____17734::uu____17735 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____17740) ->
                                 norm cfg env ((Meta (m, r)) :: stack) head1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args
                                    in
                                 norm cfg env
                                   ((Meta
                                       ((FStar_Syntax_Syntax.Meta_pattern
                                           args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____17763 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____17777 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____17777
                              | uu____17788 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____17792 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____17818 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____17836 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____17853 =
                        let uu____17854 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____17855 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____17854 uu____17855
                         in
                      failwith uu____17853
                    else rebuild cfg env stack t2
                | uu____17857 -> norm cfg env stack t2))

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
                let uu____17867 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____17867  in
              let uu____17868 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____17868 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____17881  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____17892  ->
                        let uu____17893 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____17894 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____17893 uu____17894);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        FStar_Syntax_Subst.set_use_range
                          (FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                          t
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____17907))::stack1 ->
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
                      | uu____17962 when (cfg.steps).erase_universes ->
                          norm cfg env stack t1
                      | uu____17965 ->
                          let uu____17968 =
                            let uu____17969 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____17969
                             in
                          failwith uu____17968
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
                  let uu___163_17993 = cfg  in
                  let uu____17994 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____17994;
                    tcenv = (uu___163_17993.tcenv);
                    debug = (uu___163_17993.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___163_17993.primitive_steps);
                    strong = (uu___163_17993.strong);
                    memoize_lazy = (uu___163_17993.memoize_lazy);
                    normalize_pure_lets =
                      (uu___163_17993.normalize_pure_lets)
                  }
                else
                  (let uu___164_17996 = cfg  in
                   {
                     steps =
                       (let uu___165_17999 = cfg.steps  in
                        {
                          beta = (uu___165_17999.beta);
                          iota = (uu___165_17999.iota);
                          zeta = false;
                          weak = (uu___165_17999.weak);
                          hnf = (uu___165_17999.hnf);
                          primops = (uu___165_17999.primops);
                          no_delta_steps = (uu___165_17999.no_delta_steps);
                          unfold_until = (uu___165_17999.unfold_until);
                          unfold_only = (uu___165_17999.unfold_only);
                          unfold_attr = (uu___165_17999.unfold_attr);
                          unfold_tac = (uu___165_17999.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___165_17999.pure_subterms_within_computations);
                          simplify = (uu___165_17999.simplify);
                          erase_universes = (uu___165_17999.erase_universes);
                          allow_unbound_universes =
                            (uu___165_17999.allow_unbound_universes);
                          reify_ = (uu___165_17999.reify_);
                          compress_uvars = (uu___165_17999.compress_uvars);
                          no_full_norm = (uu___165_17999.no_full_norm);
                          check_no_uvars = (uu___165_17999.check_no_uvars);
                          unmeta = (uu___165_17999.unmeta);
                          unascribe = (uu___165_17999.unascribe)
                        });
                     tcenv = (uu___164_17996.tcenv);
                     debug = (uu___164_17996.debug);
                     delta_level = (uu___164_17996.delta_level);
                     primitive_steps = (uu___164_17996.primitive_steps);
                     strong = (uu___164_17996.strong);
                     memoize_lazy = (uu___164_17996.memoize_lazy);
                     normalize_pure_lets =
                       (uu___164_17996.normalize_pure_lets)
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
                ((Meta (metadata, (head1.FStar_Syntax_Syntax.pos))) ::
                stack1) head1

and (do_reify_monadic :
  (Prims.unit -> FStar_Syntax_Syntax.term) ->
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
                  (fun uu____18029  ->
                     let uu____18030 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____18031 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____18030
                       uu____18031);
                (let uu____18032 =
                   let uu____18033 = FStar_Syntax_Subst.compress head2  in
                   uu____18033.FStar_Syntax_Syntax.n  in
                 match uu____18032 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____18051 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18051 with
                      | (uu____18052,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____18058 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____18066 =
                                   let uu____18067 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____18067.FStar_Syntax_Syntax.n  in
                                 match uu____18066 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____18073,uu____18074))
                                     ->
                                     let uu____18083 =
                                       let uu____18084 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____18084.FStar_Syntax_Syntax.n  in
                                     (match uu____18083 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____18090,msrc,uu____18092))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____18101 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____18101
                                      | uu____18102 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____18103 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____18104 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____18104 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___166_18109 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___166_18109.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___166_18109.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___166_18109.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___166_18109.FStar_Syntax_Syntax.lbattrs)
                                      }  in
                                    let uu____18110 = FStar_List.tl stack  in
                                    let uu____18111 =
                                      let uu____18112 =
                                        let uu____18115 =
                                          let uu____18116 =
                                            let uu____18129 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____18129)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____18116
                                           in
                                        FStar_Syntax_Syntax.mk uu____18115
                                         in
                                      uu____18112
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____18110 uu____18111
                                | FStar_Pervasives_Native.None  ->
                                    let uu____18145 =
                                      let uu____18146 = is_return body  in
                                      match uu____18146 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____18150;
                                            FStar_Syntax_Syntax.vars =
                                              uu____18151;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____18156 -> false  in
                                    if uu____18145
                                    then
                                      norm cfg env stack
                                        lb.FStar_Syntax_Syntax.lbdef
                                    else
                                      (let rng =
                                         head2.FStar_Syntax_Syntax.pos  in
                                       let head3 =
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
                                         let uu____18179 =
                                           let uu____18182 =
                                             let uu____18183 =
                                               let uu____18200 =
                                                 let uu____18203 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____18203]  in
                                               (uu____18200, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____18183
                                              in
                                           FStar_Syntax_Syntax.mk uu____18182
                                            in
                                         uu____18179
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____18219 =
                                           let uu____18220 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____18220.FStar_Syntax_Syntax.n
                                            in
                                         match uu____18219 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____18226::uu____18227::[])
                                             ->
                                             let uu____18234 =
                                               let uu____18237 =
                                                 let uu____18238 =
                                                   let uu____18245 =
                                                     let uu____18248 =
                                                       let uu____18249 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____18249
                                                        in
                                                     let uu____18250 =
                                                       let uu____18253 =
                                                         let uu____18254 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____18254
                                                          in
                                                       [uu____18253]  in
                                                     uu____18248 ::
                                                       uu____18250
                                                      in
                                                   (bind1, uu____18245)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____18238
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____18237
                                                in
                                             uu____18234
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____18262 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let reified =
                                         let uu____18268 =
                                           let uu____18271 =
                                             let uu____18272 =
                                               let uu____18287 =
                                                 let uu____18290 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____18291 =
                                                   let uu____18294 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   let uu____18295 =
                                                     let uu____18298 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____18299 =
                                                       let uu____18302 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3
                                                          in
                                                       let uu____18303 =
                                                         let uu____18306 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____18307 =
                                                           let uu____18310 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____18310]  in
                                                         uu____18306 ::
                                                           uu____18307
                                                          in
                                                       uu____18302 ::
                                                         uu____18303
                                                        in
                                                     uu____18298 ::
                                                       uu____18299
                                                      in
                                                   uu____18294 :: uu____18295
                                                    in
                                                 uu____18290 :: uu____18291
                                                  in
                                               (bind_inst, uu____18287)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____18272
                                              in
                                           FStar_Syntax_Syntax.mk uu____18271
                                            in
                                         uu____18268
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____18322  ->
                                            let uu____18323 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____18324 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____18323 uu____18324);
                                       (let uu____18325 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____18325 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m  in
                     let uu____18349 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18349 with
                      | (uu____18350,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____18385 =
                                  let uu____18386 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____18386.FStar_Syntax_Syntax.n  in
                                match uu____18385 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____18392) -> t2
                                | uu____18397 -> head3  in
                              let uu____18398 =
                                let uu____18399 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____18399.FStar_Syntax_Syntax.n  in
                              match uu____18398 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____18405 -> FStar_Pervasives_Native.None
                               in
                            let uu____18406 = maybe_extract_fv head3  in
                            match uu____18406 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____18416 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____18416
                                ->
                                let head4 = norm cfg env [] head3  in
                                let action_unfolded =
                                  let uu____18421 = maybe_extract_fv head4
                                     in
                                  match uu____18421 with
                                  | FStar_Pervasives_Native.Some uu____18426
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____18427 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head4, action_unfolded)
                            | uu____18432 ->
                                (head3, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____18447 =
                              match uu____18447 with
                              | (e,q) ->
                                  let uu____18454 =
                                    let uu____18455 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____18455.FStar_Syntax_Syntax.n  in
                                  (match uu____18454 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____18470 -> false)
                               in
                            let uu____18471 =
                              let uu____18472 =
                                let uu____18479 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____18479 :: args  in
                              FStar_Util.for_some is_arg_impure uu____18472
                               in
                            if uu____18471
                            then
                              let uu____18484 =
                                let uu____18485 =
                                  FStar_Syntax_Print.term_to_string head2  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____18485
                                 in
                              failwith uu____18484
                            else ());
                           (let uu____18487 = maybe_unfold_action head_app
                               in
                            match uu____18487 with
                            | (head_app1,found_action) ->
                                let mk1 tm =
                                  FStar_Syntax_Syntax.mk tm
                                    FStar_Pervasives_Native.None
                                    head2.FStar_Syntax_Syntax.pos
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
                                   (fun uu____18528  ->
                                      let uu____18529 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____18530 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____18529 uu____18530);
                                 (let uu____18531 = FStar_List.tl stack  in
                                  norm cfg env uu____18531 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____18533) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____18557 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____18557  in
                     (log cfg
                        (fun uu____18561  ->
                           let uu____18562 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____18562);
                      (let uu____18563 = FStar_List.tl stack  in
                       norm cfg env uu____18563 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____18565) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____18690  ->
                               match uu____18690 with
                               | (pat,wopt,tm) ->
                                   let uu____18738 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____18738)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos
                        in
                     let uu____18770 = FStar_List.tl stack  in
                     norm cfg env uu____18770 tm
                 | uu____18771 -> fallback ())

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
              (fun uu____18785  ->
                 let uu____18786 = FStar_Ident.string_of_lid msrc  in
                 let uu____18787 = FStar_Ident.string_of_lid mtgt  in
                 let uu____18788 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____18786
                   uu____18787 uu____18788);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed = FStar_TypeChecker_Env.get_effect_decl env mtgt  in
               let uu____18790 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____18790 with
               | (uu____18791,return_repr) ->
                   let return_inst =
                     let uu____18800 =
                       let uu____18801 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____18801.FStar_Syntax_Syntax.n  in
                     match uu____18800 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____18807::[]) ->
                         let uu____18814 =
                           let uu____18817 =
                             let uu____18818 =
                               let uu____18825 =
                                 let uu____18828 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____18828]  in
                               (return_tm, uu____18825)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____18818  in
                           FStar_Syntax_Syntax.mk uu____18817  in
                         uu____18814 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____18836 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____18839 =
                     let uu____18842 =
                       let uu____18843 =
                         let uu____18858 =
                           let uu____18861 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____18862 =
                             let uu____18865 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____18865]  in
                           uu____18861 :: uu____18862  in
                         (return_inst, uu____18858)  in
                       FStar_Syntax_Syntax.Tm_app uu____18843  in
                     FStar_Syntax_Syntax.mk uu____18842  in
                   uu____18839 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____18874 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____18874 with
               | FStar_Pervasives_Native.None  ->
                   let uu____18877 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____18877
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____18878;
                     FStar_TypeChecker_Env.mtarget = uu____18879;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____18880;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____18895 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____18895
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____18896;
                     FStar_TypeChecker_Env.mtarget = uu____18897;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____18898;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____18922 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____18923 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____18922 t FStar_Syntax_Syntax.tun uu____18923)

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
                (fun uu____18979  ->
                   match uu____18979 with
                   | (a,imp) ->
                       let uu____18990 = norm cfg env [] a  in
                       (uu____18990, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___167_19004 = comp  in
            let uu____19005 =
              let uu____19006 =
                let uu____19015 = norm cfg env [] t  in
                let uu____19016 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____19015, uu____19016)  in
              FStar_Syntax_Syntax.Total uu____19006  in
            {
              FStar_Syntax_Syntax.n = uu____19005;
              FStar_Syntax_Syntax.pos =
                (uu___167_19004.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___167_19004.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___168_19031 = comp  in
            let uu____19032 =
              let uu____19033 =
                let uu____19042 = norm cfg env [] t  in
                let uu____19043 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____19042, uu____19043)  in
              FStar_Syntax_Syntax.GTotal uu____19033  in
            {
              FStar_Syntax_Syntax.n = uu____19032;
              FStar_Syntax_Syntax.pos =
                (uu___168_19031.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___168_19031.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____19095  ->
                      match uu____19095 with
                      | (a,i) ->
                          let uu____19106 = norm cfg env [] a  in
                          (uu____19106, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___88_19117  ->
                      match uu___88_19117 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____19121 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____19121
                      | f -> f))
               in
            let uu___169_19125 = comp  in
            let uu____19126 =
              let uu____19127 =
                let uu___170_19128 = ct  in
                let uu____19129 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____19130 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____19133 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____19129;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___170_19128.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____19130;
                  FStar_Syntax_Syntax.effect_args = uu____19133;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____19127  in
            {
              FStar_Syntax_Syntax.n = uu____19126;
              FStar_Syntax_Syntax.pos =
                (uu___169_19125.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___169_19125.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____19144  ->
        match uu____19144 with
        | (x,imp) ->
            let uu____19147 =
              let uu___171_19148 = x  in
              let uu____19149 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___171_19148.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___171_19148.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____19149
              }  in
            (uu____19147, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____19155 =
          FStar_List.fold_left
            (fun uu____19173  ->
               fun b  ->
                 match uu____19173 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____19155 with | (nbs,uu____19213) -> FStar_List.rev nbs

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
            let uu____19229 =
              let uu___172_19230 = rc  in
              let uu____19231 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___172_19230.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____19231;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___172_19230.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____19229
        | uu____19238 -> lopt

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____19251  ->
               let uu____19252 = FStar_Syntax_Print.tag_of_term t  in
               let uu____19253 = FStar_Syntax_Print.term_to_string t  in
               let uu____19254 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____19261 =
                 let uu____19262 =
                   let uu____19265 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____19265
                    in
                 stack_to_string uu____19262  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____19252 uu____19253 uu____19254 uu____19261);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____19296 =
                     let uu____19297 =
                       let uu____19298 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____19298  in
                     FStar_Util.string_of_int uu____19297  in
                   let uu____19303 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____19304 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____19296 uu____19303 uu____19304)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____19358  ->
                     let uu____19359 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____19359);
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
               let uu____19395 =
                 let uu___173_19396 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___173_19396.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___173_19396.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____19395
           | (Arg (Univ uu____19397,uu____19398,uu____19399))::uu____19400 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____19403,uu____19404))::uu____19405 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____19420,uu____19421),aq,r))::stack1
               when
               ((let uu____19473 = head_of t1  in
                 FStar_Syntax_Util.is_fstar_tactics_quote uu____19473) ||
                  (is_embed_position_1 t1))
                 ||
                 (let uu____19475 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____19475)
               ->
               let t2 =
                 let uu____19479 =
                   let uu____19480 =
                     let uu____19481 = closure_as_term cfg env_arg tm  in
                     (uu____19481, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____19480  in
                 uu____19479 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____19487),aq,r))::stack1 ->
               (log cfg
                  (fun uu____19540  ->
                     let uu____19541 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____19541);
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
                  (let uu____19551 = FStar_ST.op_Bang m  in
                   match uu____19551 with
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
                   | FStar_Pervasives_Native.Some (uu____19688,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____19735 =
                 log cfg
                   (fun uu____19739  ->
                      let uu____19740 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____19740);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____19744 =
                 let uu____19745 = FStar_Syntax_Subst.compress t1  in
                 uu____19745.FStar_Syntax_Syntax.n  in
               (match uu____19744 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____19772 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____19772  in
                    (log cfg
                       (fun uu____19776  ->
                          let uu____19777 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____19777);
                     (let uu____19778 = FStar_List.tl stack  in
                      norm cfg env1 uu____19778 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____19779);
                       FStar_Syntax_Syntax.pos = uu____19780;
                       FStar_Syntax_Syntax.vars = uu____19781;_},(e,uu____19783)::[])
                    -> norm cfg env1 stack' e
                | uu____19812 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____19832  ->
                     let uu____19833 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____19833);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____19838 =
                   log cfg
                     (fun uu____19843  ->
                        let uu____19844 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____19845 =
                          let uu____19846 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____19863  ->
                                    match uu____19863 with
                                    | (p,uu____19873,uu____19874) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____19846
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____19844 uu____19845);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___89_19891  ->
                                match uu___89_19891 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____19892 -> false))
                         in
                      let uu___174_19893 = cfg  in
                      {
                        steps =
                          (let uu___175_19896 = cfg.steps  in
                           {
                             beta = (uu___175_19896.beta);
                             iota = (uu___175_19896.iota);
                             zeta = false;
                             weak = (uu___175_19896.weak);
                             hnf = (uu___175_19896.hnf);
                             primops = (uu___175_19896.primops);
                             no_delta_steps = (uu___175_19896.no_delta_steps);
                             unfold_until = (uu___175_19896.unfold_until);
                             unfold_only = (uu___175_19896.unfold_only);
                             unfold_attr = (uu___175_19896.unfold_attr);
                             unfold_tac = (uu___175_19896.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___175_19896.pure_subterms_within_computations);
                             simplify = (uu___175_19896.simplify);
                             erase_universes =
                               (uu___175_19896.erase_universes);
                             allow_unbound_universes =
                               (uu___175_19896.allow_unbound_universes);
                             reify_ = (uu___175_19896.reify_);
                             compress_uvars = (uu___175_19896.compress_uvars);
                             no_full_norm = (uu___175_19896.no_full_norm);
                             check_no_uvars = (uu___175_19896.check_no_uvars);
                             unmeta = (uu___175_19896.unmeta);
                             unascribe = (uu___175_19896.unascribe)
                           });
                        tcenv = (uu___174_19893.tcenv);
                        debug = (uu___174_19893.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___174_19893.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___174_19893.memoize_lazy);
                        normalize_pure_lets =
                          (uu___174_19893.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____19928 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____19949 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____20009  ->
                                    fun uu____20010  ->
                                      match (uu____20009, uu____20010) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____20101 = norm_pat env3 p1
                                             in
                                          (match uu____20101 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____19949 with
                           | (pats1,env3) ->
                               ((let uu___176_20183 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___176_20183.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___177_20202 = x  in
                            let uu____20203 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___177_20202.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___177_20202.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20203
                            }  in
                          ((let uu___178_20217 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___178_20217.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___179_20228 = x  in
                            let uu____20229 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___179_20228.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___179_20228.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20229
                            }  in
                          ((let uu___180_20243 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___180_20243.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___181_20259 = x  in
                            let uu____20260 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___181_20259.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___181_20259.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20260
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___182_20267 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___182_20267.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____20277 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____20291 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____20291 with
                                  | (p,wopt,e) ->
                                      let uu____20311 = norm_pat env1 p  in
                                      (match uu____20311 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____20336 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____20336
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____20342 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____20342)
                    in
                 let rec is_cons head1 =
                   let uu____20347 =
                     let uu____20348 = FStar_Syntax_Subst.compress head1  in
                     uu____20348.FStar_Syntax_Syntax.n  in
                   match uu____20347 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____20352) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____20357 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20358;
                         FStar_Syntax_Syntax.fv_delta = uu____20359;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20360;
                         FStar_Syntax_Syntax.fv_delta = uu____20361;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____20362);_}
                       -> true
                   | uu____20369 -> false  in
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
                   let uu____20514 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____20514 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____20601 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____20640 ->
                                 let uu____20641 =
                                   let uu____20642 = is_cons head1  in
                                   Prims.op_Negation uu____20642  in
                                 FStar_Util.Inr uu____20641)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____20667 =
                              let uu____20668 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____20668.FStar_Syntax_Syntax.n  in
                            (match uu____20667 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____20686 ->
                                 let uu____20687 =
                                   let uu____20688 = is_cons head1  in
                                   Prims.op_Negation uu____20688  in
                                 FStar_Util.Inr uu____20687))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____20757)::rest_a,(p1,uu____20760)::rest_p) ->
                       let uu____20804 = matches_pat t2 p1  in
                       (match uu____20804 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____20853 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____20959 = matches_pat scrutinee1 p1  in
                       (match uu____20959 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____20999  ->
                                  let uu____21000 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____21001 =
                                    let uu____21002 =
                                      FStar_List.map
                                        (fun uu____21012  ->
                                           match uu____21012 with
                                           | (uu____21017,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____21002
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____21000 uu____21001);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____21048  ->
                                       match uu____21048 with
                                       | (bv,t2) ->
                                           let uu____21071 =
                                             let uu____21078 =
                                               let uu____21081 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____21081
                                                in
                                             let uu____21082 =
                                               let uu____21083 =
                                                 let uu____21114 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____21114, false)
                                                  in
                                               Clos uu____21083  in
                                             (uu____21078, uu____21082)  in
                                           uu____21071 :: env2) env1 s
                                 in
                              let uu____21231 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____21231)))
                    in
                 if (cfg.steps).iota
                 then matches scrutinee branches
                 else norm_and_rebuild_match ())))

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
               (fun uu___90_21259  ->
                  match uu___90_21259 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____21263 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____21269 -> d  in
        let uu____21272 = to_fsteps s  in
        let uu____21273 =
          let uu____21274 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____21275 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____21276 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____21277 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____21278 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____21274;
            primop = uu____21275;
            b380 = uu____21276;
            norm_delayed = uu____21277;
            print_normalized = uu____21278
          }  in
        let uu____21279 = add_steps built_in_primitive_steps psteps  in
        let uu____21282 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____21284 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____21284)
           in
        {
          steps = uu____21272;
          tcenv = e;
          debug = uu____21273;
          delta_level = d1;
          primitive_steps = uu____21279;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____21282
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
      fun t  -> let uu____21342 = config s e  in norm_comp uu____21342 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____21355 = config [] env  in norm_universe uu____21355 [] u
  
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
        let uu____21373 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21373  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____21380 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___183_21399 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___183_21399.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___183_21399.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____21406 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____21406
          then
            let ct1 =
              match downgrade_ghost_effect_name
                      ct.FStar_Syntax_Syntax.effect_name
              with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    if
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___184_21415 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___184_21415.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___184_21415.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___184_21415.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___185_21417 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___185_21417.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___185_21417.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___185_21417.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___185_21417.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___186_21418 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___186_21418.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___186_21418.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____21420 -> c
  
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
        let uu____21432 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21432  in
      let uu____21439 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____21439
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____21443  ->
                 let uu____21444 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____21444)
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
            ((let uu____21461 =
                let uu____21466 =
                  let uu____21467 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____21467
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____21466)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____21461);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____21478 = config [AllowUnboundUniverses] env  in
          norm_comp uu____21478 [] c
        with
        | e ->
            ((let uu____21491 =
                let uu____21496 =
                  let uu____21497 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____21497
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____21496)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____21491);
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
                   let uu____21534 =
                     let uu____21535 =
                       let uu____21542 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____21542)  in
                     FStar_Syntax_Syntax.Tm_refine uu____21535  in
                   mk uu____21534 t01.FStar_Syntax_Syntax.pos
               | uu____21547 -> t2)
          | uu____21548 -> t2  in
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
             NoDeltaSteps;
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
        let uu____21588 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____21588 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____21617 ->
                 let uu____21624 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____21624 with
                  | (actuals,uu____21634,uu____21635) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____21649 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____21649 with
                         | (binders,args) ->
                             let uu____21666 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____21666
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
      | uu____21674 ->
          let uu____21675 = FStar_Syntax_Util.head_and_args t  in
          (match uu____21675 with
           | (head1,args) ->
               let uu____21712 =
                 let uu____21713 = FStar_Syntax_Subst.compress head1  in
                 uu____21713.FStar_Syntax_Syntax.n  in
               (match uu____21712 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____21716,thead) ->
                    let uu____21742 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____21742 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____21784 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___191_21792 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___191_21792.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___191_21792.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___191_21792.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___191_21792.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___191_21792.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___191_21792.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___191_21792.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___191_21792.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___191_21792.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___191_21792.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___191_21792.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___191_21792.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___191_21792.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___191_21792.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___191_21792.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___191_21792.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___191_21792.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___191_21792.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___191_21792.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___191_21792.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___191_21792.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___191_21792.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___191_21792.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___191_21792.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___191_21792.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___191_21792.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___191_21792.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___191_21792.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___191_21792.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___191_21792.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___191_21792.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___191_21792.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____21784 with
                            | (uu____21793,ty,uu____21795) ->
                                eta_expand_with_type env t ty))
                | uu____21796 ->
                    let uu____21797 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___192_21805 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___192_21805.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___192_21805.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___192_21805.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___192_21805.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___192_21805.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___192_21805.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___192_21805.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___192_21805.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___192_21805.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___192_21805.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___192_21805.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___192_21805.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___192_21805.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___192_21805.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___192_21805.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___192_21805.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___192_21805.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___192_21805.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___192_21805.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___192_21805.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___192_21805.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___192_21805.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___192_21805.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___192_21805.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___192_21805.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___192_21805.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___192_21805.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___192_21805.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___192_21805.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___192_21805.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___192_21805.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___192_21805.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____21797 with
                     | (uu____21806,ty,uu____21808) ->
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
      let uu___193_21865 = x  in
      let uu____21866 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___193_21865.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___193_21865.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____21866
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____21869 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____21894 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____21895 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____21896 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____21897 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____21904 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____21905 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____21906 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___194_21934 = rc  in
          let uu____21935 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____21942 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___194_21934.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____21935;
            FStar_Syntax_Syntax.residual_flags = uu____21942
          }  in
        let uu____21945 =
          let uu____21946 =
            let uu____21963 = elim_delayed_subst_binders bs  in
            let uu____21970 = elim_delayed_subst_term t2  in
            let uu____21971 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____21963, uu____21970, uu____21971)  in
          FStar_Syntax_Syntax.Tm_abs uu____21946  in
        mk1 uu____21945
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____22000 =
          let uu____22001 =
            let uu____22014 = elim_delayed_subst_binders bs  in
            let uu____22021 = elim_delayed_subst_comp c  in
            (uu____22014, uu____22021)  in
          FStar_Syntax_Syntax.Tm_arrow uu____22001  in
        mk1 uu____22000
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____22034 =
          let uu____22035 =
            let uu____22042 = elim_bv bv  in
            let uu____22043 = elim_delayed_subst_term phi  in
            (uu____22042, uu____22043)  in
          FStar_Syntax_Syntax.Tm_refine uu____22035  in
        mk1 uu____22034
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____22066 =
          let uu____22067 =
            let uu____22082 = elim_delayed_subst_term t2  in
            let uu____22083 = elim_delayed_subst_args args  in
            (uu____22082, uu____22083)  in
          FStar_Syntax_Syntax.Tm_app uu____22067  in
        mk1 uu____22066
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___195_22147 = p  in
              let uu____22148 =
                let uu____22149 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____22149  in
              {
                FStar_Syntax_Syntax.v = uu____22148;
                FStar_Syntax_Syntax.p =
                  (uu___195_22147.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___196_22151 = p  in
              let uu____22152 =
                let uu____22153 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____22153  in
              {
                FStar_Syntax_Syntax.v = uu____22152;
                FStar_Syntax_Syntax.p =
                  (uu___196_22151.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___197_22160 = p  in
              let uu____22161 =
                let uu____22162 =
                  let uu____22169 = elim_bv x  in
                  let uu____22170 = elim_delayed_subst_term t0  in
                  (uu____22169, uu____22170)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____22162  in
              {
                FStar_Syntax_Syntax.v = uu____22161;
                FStar_Syntax_Syntax.p =
                  (uu___197_22160.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___198_22189 = p  in
              let uu____22190 =
                let uu____22191 =
                  let uu____22204 =
                    FStar_List.map
                      (fun uu____22227  ->
                         match uu____22227 with
                         | (x,b) ->
                             let uu____22240 = elim_pat x  in
                             (uu____22240, b)) pats
                     in
                  (fv, uu____22204)  in
                FStar_Syntax_Syntax.Pat_cons uu____22191  in
              {
                FStar_Syntax_Syntax.v = uu____22190;
                FStar_Syntax_Syntax.p =
                  (uu___198_22189.FStar_Syntax_Syntax.p)
              }
          | uu____22253 -> p  in
        let elim_branch uu____22275 =
          match uu____22275 with
          | (pat,wopt,t3) ->
              let uu____22301 = elim_pat pat  in
              let uu____22304 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____22307 = elim_delayed_subst_term t3  in
              (uu____22301, uu____22304, uu____22307)
           in
        let uu____22312 =
          let uu____22313 =
            let uu____22336 = elim_delayed_subst_term t2  in
            let uu____22337 = FStar_List.map elim_branch branches  in
            (uu____22336, uu____22337)  in
          FStar_Syntax_Syntax.Tm_match uu____22313  in
        mk1 uu____22312
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____22446 =
          match uu____22446 with
          | (tc,topt) ->
              let uu____22481 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____22491 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____22491
                | FStar_Util.Inr c ->
                    let uu____22493 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____22493
                 in
              let uu____22494 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____22481, uu____22494)
           in
        let uu____22503 =
          let uu____22504 =
            let uu____22531 = elim_delayed_subst_term t2  in
            let uu____22532 = elim_ascription a  in
            (uu____22531, uu____22532, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____22504  in
        mk1 uu____22503
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___199_22577 = lb  in
          let uu____22578 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____22581 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___199_22577.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___199_22577.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____22578;
            FStar_Syntax_Syntax.lbeff =
              (uu___199_22577.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____22581;
            FStar_Syntax_Syntax.lbattrs =
              (uu___199_22577.FStar_Syntax_Syntax.lbattrs)
          }  in
        let uu____22584 =
          let uu____22585 =
            let uu____22598 =
              let uu____22605 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____22605)  in
            let uu____22614 = elim_delayed_subst_term t2  in
            (uu____22598, uu____22614)  in
          FStar_Syntax_Syntax.Tm_let uu____22585  in
        mk1 uu____22584
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____22647 =
          let uu____22648 =
            let uu____22665 = elim_delayed_subst_term t2  in
            (uv, uu____22665)  in
          FStar_Syntax_Syntax.Tm_uvar uu____22648  in
        mk1 uu____22647
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____22682 =
          let uu____22683 =
            let uu____22690 = elim_delayed_subst_term t2  in
            let uu____22691 = elim_delayed_subst_meta md  in
            (uu____22690, uu____22691)  in
          FStar_Syntax_Syntax.Tm_meta uu____22683  in
        mk1 uu____22682

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___91_22698  ->
         match uu___91_22698 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____22702 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____22702
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
        let uu____22723 =
          let uu____22724 =
            let uu____22733 = elim_delayed_subst_term t  in
            (uu____22733, uopt)  in
          FStar_Syntax_Syntax.Total uu____22724  in
        mk1 uu____22723
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____22746 =
          let uu____22747 =
            let uu____22756 = elim_delayed_subst_term t  in
            (uu____22756, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____22747  in
        mk1 uu____22746
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___200_22761 = ct  in
          let uu____22762 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____22765 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____22774 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___200_22761.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___200_22761.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____22762;
            FStar_Syntax_Syntax.effect_args = uu____22765;
            FStar_Syntax_Syntax.flags = uu____22774
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___92_22777  ->
    match uu___92_22777 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____22789 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____22789
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____22822 =
          let uu____22829 = elim_delayed_subst_term t  in (m, uu____22829)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____22822
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____22837 =
          let uu____22846 = elim_delayed_subst_term t  in
          (m1, m2, uu____22846)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____22837
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____22869  ->
         match uu____22869 with
         | (t,q) ->
             let uu____22880 = elim_delayed_subst_term t  in (uu____22880, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____22900  ->
         match uu____22900 with
         | (x,q) ->
             let uu____22911 =
               let uu___201_22912 = x  in
               let uu____22913 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___201_22912.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___201_22912.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____22913
               }  in
             (uu____22911, q)) bs

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
            | (uu____22989,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____22995,FStar_Util.Inl t) ->
                let uu____23001 =
                  let uu____23004 =
                    let uu____23005 =
                      let uu____23018 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____23018)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____23005  in
                  FStar_Syntax_Syntax.mk uu____23004  in
                uu____23001 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____23022 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____23022 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____23050 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____23105 ->
                    let uu____23106 =
                      let uu____23115 =
                        let uu____23116 = FStar_Syntax_Subst.compress t4  in
                        uu____23116.FStar_Syntax_Syntax.n  in
                      (uu____23115, tc)  in
                    (match uu____23106 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____23141) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____23178) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____23217,FStar_Util.Inl uu____23218) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____23241 -> failwith "Impossible")
                 in
              (match uu____23050 with
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
          let uu____23346 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____23346 with
          | (univ_names1,binders1,tc) ->
              let uu____23404 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____23404)
  
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
          let uu____23439 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____23439 with
          | (univ_names1,binders1,tc) ->
              let uu____23499 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____23499)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____23532 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____23532 with
           | (univ_names1,binders1,typ1) ->
               let uu___202_23560 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___202_23560.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___202_23560.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___202_23560.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___202_23560.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___203_23581 = s  in
          let uu____23582 =
            let uu____23583 =
              let uu____23592 = FStar_List.map (elim_uvars env) sigs  in
              (uu____23592, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____23583  in
          {
            FStar_Syntax_Syntax.sigel = uu____23582;
            FStar_Syntax_Syntax.sigrng =
              (uu___203_23581.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___203_23581.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___203_23581.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___203_23581.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____23609 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____23609 with
           | (univ_names1,uu____23627,typ1) ->
               let uu___204_23641 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___204_23641.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___204_23641.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___204_23641.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___204_23641.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____23647 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____23647 with
           | (univ_names1,uu____23665,typ1) ->
               let uu___205_23679 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___205_23679.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___205_23679.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___205_23679.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___205_23679.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____23713 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____23713 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____23736 =
                            let uu____23737 =
                              let uu____23738 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____23738  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____23737
                             in
                          elim_delayed_subst_term uu____23736  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___206_23741 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___206_23741.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___206_23741.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___206_23741.FStar_Syntax_Syntax.lbattrs)
                        }))
             in
          let uu___207_23742 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___207_23742.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___207_23742.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___207_23742.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___207_23742.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___208_23754 = s  in
          let uu____23755 =
            let uu____23756 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____23756  in
          {
            FStar_Syntax_Syntax.sigel = uu____23755;
            FStar_Syntax_Syntax.sigrng =
              (uu___208_23754.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___208_23754.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___208_23754.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___208_23754.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____23760 = elim_uvars_aux_t env us [] t  in
          (match uu____23760 with
           | (us1,uu____23778,t1) ->
               let uu___209_23792 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___209_23792.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___209_23792.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___209_23792.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___209_23792.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____23793 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____23795 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____23795 with
           | (univs1,binders,signature) ->
               let uu____23823 =
                 let uu____23832 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____23832 with
                 | (univs_opening,univs2) ->
                     let uu____23859 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____23859)
                  in
               (match uu____23823 with
                | (univs_opening,univs_closing) ->
                    let uu____23876 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____23882 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____23883 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____23882, uu____23883)  in
                    (match uu____23876 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____23905 =
                           match uu____23905 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____23923 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____23923 with
                                | (us1,t1) ->
                                    let uu____23934 =
                                      let uu____23939 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____23946 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____23939, uu____23946)  in
                                    (match uu____23934 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____23959 =
                                           let uu____23964 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____23973 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____23964, uu____23973)  in
                                         (match uu____23959 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____23989 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____23989
                                                 in
                                              let uu____23990 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____23990 with
                                               | (uu____24011,uu____24012,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____24027 =
                                                       let uu____24028 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____24028
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____24027
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____24033 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____24033 with
                           | (uu____24046,uu____24047,t1) -> t1  in
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
                             | uu____24107 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____24124 =
                               let uu____24125 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____24125.FStar_Syntax_Syntax.n  in
                             match uu____24124 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____24184 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____24213 =
                               let uu____24214 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____24214.FStar_Syntax_Syntax.n  in
                             match uu____24213 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____24235) ->
                                 let uu____24256 = destruct_action_body body
                                    in
                                 (match uu____24256 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____24301 ->
                                 let uu____24302 = destruct_action_body t  in
                                 (match uu____24302 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____24351 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____24351 with
                           | (action_univs,t) ->
                               let uu____24360 = destruct_action_typ_templ t
                                  in
                               (match uu____24360 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___210_24401 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___210_24401.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___210_24401.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___211_24403 = ed  in
                           let uu____24404 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____24405 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____24406 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____24407 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____24408 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____24409 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____24410 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____24411 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____24412 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____24413 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____24414 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____24415 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____24416 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____24417 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___211_24403.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___211_24403.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____24404;
                             FStar_Syntax_Syntax.bind_wp = uu____24405;
                             FStar_Syntax_Syntax.if_then_else = uu____24406;
                             FStar_Syntax_Syntax.ite_wp = uu____24407;
                             FStar_Syntax_Syntax.stronger = uu____24408;
                             FStar_Syntax_Syntax.close_wp = uu____24409;
                             FStar_Syntax_Syntax.assert_p = uu____24410;
                             FStar_Syntax_Syntax.assume_p = uu____24411;
                             FStar_Syntax_Syntax.null_wp = uu____24412;
                             FStar_Syntax_Syntax.trivial = uu____24413;
                             FStar_Syntax_Syntax.repr = uu____24414;
                             FStar_Syntax_Syntax.return_repr = uu____24415;
                             FStar_Syntax_Syntax.bind_repr = uu____24416;
                             FStar_Syntax_Syntax.actions = uu____24417
                           }  in
                         let uu___212_24420 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___212_24420.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___212_24420.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___212_24420.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___212_24420.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___93_24437 =
            match uu___93_24437 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____24464 = elim_uvars_aux_t env us [] t  in
                (match uu____24464 with
                 | (us1,uu____24488,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___213_24507 = sub_eff  in
            let uu____24508 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____24511 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___213_24507.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___213_24507.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____24508;
              FStar_Syntax_Syntax.lift = uu____24511
            }  in
          let uu___214_24514 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___214_24514.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___214_24514.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___214_24514.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___214_24514.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____24524 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____24524 with
           | (univ_names1,binders1,comp1) ->
               let uu___215_24558 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___215_24558.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___215_24558.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___215_24558.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___215_24558.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____24569 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  