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
    ('Auu____162 -> 'Auu____163) ->
      'Auu____163 ->
        'Auu____162 FStar_Pervasives_Native.option -> 'Auu____163
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
    match projectee with | Clos _0 -> true | uu____1371 -> false
  
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
    match projectee with | Univ _0 -> true | uu____1473 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1484 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
let (closure_to_string : closure -> Prims.string) =
  fun uu___77_1503  ->
    match uu___77_1503 with
    | Clos (uu____1504,t,uu____1506,uu____1507) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____1552 -> "Univ"
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
    let uu____1814 = FStar_Util.psmap_empty ()  in add_steps uu____1814 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      FStar_Util.psmap_try_find cfg.primitive_steps
        (FStar_Ident.text_of_lid
           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
  
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
    match projectee with | Arg _0 -> true | uu____1966 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2002 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2038 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2107 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2149 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2205 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2245 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2277 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2313 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2329 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2354 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2354 with | (hd1,uu____2368) -> hd1
  
let mk :
  'Auu____2388 .
    'Auu____2388 ->
      FStar_Range.range -> 'Auu____2388 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2442 = FStar_ST.op_Bang r  in
          match uu____2442 with
          | FStar_Pervasives_Native.Some uu____2490 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2544 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2544 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___78_2551  ->
    match uu___78_2551 with
    | Arg (c,uu____2553,uu____2554) ->
        let uu____2555 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2555
    | MemoLazy uu____2556 -> "MemoLazy"
    | Abs (uu____2563,bs,uu____2565,uu____2566,uu____2567) ->
        let uu____2572 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2572
    | UnivArgs uu____2577 -> "UnivArgs"
    | Match uu____2584 -> "Match"
    | App (uu____2591,t,uu____2593,uu____2594) ->
        let uu____2595 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2595
    | Meta (m,uu____2597) -> "Meta"
    | Let uu____2598 -> "Let"
    | Cfg uu____2607 -> "Cfg"
    | Debug (t,uu____2609) ->
        let uu____2610 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2610
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2618 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2618 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2649 . 'Auu____2649 Prims.list -> Prims.bool =
  fun uu___79_2655  ->
    match uu___79_2655 with | [] -> true | uu____2658 -> false
  
let lookup_bvar :
  'Auu____2665 'Auu____2666 .
    ('Auu____2665,'Auu____2666) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2666
  =
  fun env  ->
    fun x  ->
      try
        let uu____2690 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____2690
      with
      | uu____2703 ->
          let uu____2704 =
            let uu____2705 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____2705  in
          failwith uu____2704
  
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
          let uu____2742 =
            FStar_List.fold_left
              (fun uu____2768  ->
                 fun u1  ->
                   match uu____2768 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2793 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2793 with
                        | (k_u,n1) ->
                            let uu____2808 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____2808
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2742 with
          | (uu____2826,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2851 =
                   let uu____2852 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____2852  in
                 match uu____2851 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2870 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2878 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2884 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2893 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2902 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2909 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2909 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2926 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2926 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2934 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2942 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____2942 with
                                  | (uu____2947,m) -> n1 <= m))
                           in
                        if uu____2934 then rest1 else us1
                    | uu____2952 -> us1)
               | uu____2957 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2961 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____2961
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2965 = aux u  in
           match uu____2965 with
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
          (fun uu____3069  ->
             let uu____3070 = FStar_Syntax_Print.tag_of_term t  in
             let uu____3071 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3070
               uu____3071);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3078 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3080 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3105 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3106 -> t1
              | FStar_Syntax_Syntax.Tm_lazy uu____3107 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3108 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3109 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3126 =
                      let uu____3127 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____3128 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3127 uu____3128
                       in
                    failwith uu____3126
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3131 =
                    let uu____3132 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____3132  in
                  mk uu____3131 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3139 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3139
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3141 = lookup_bvar env x  in
                  (match uu____3141 with
                   | Univ uu____3144 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3147,uu____3148) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3260 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3260 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____3288 =
                         let uu____3289 =
                           let uu____3306 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____3306)  in
                         FStar_Syntax_Syntax.Tm_abs uu____3289  in
                       mk uu____3288 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3337 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3337 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3379 =
                    let uu____3390 =
                      let uu____3397 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3397]  in
                    closures_as_binders_delayed cfg env uu____3390  in
                  (match uu____3379 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____3415 =
                         let uu____3416 =
                           let uu____3423 =
                             let uu____3424 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____3424
                               FStar_Pervasives_Native.fst
                              in
                           (uu____3423, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____3416  in
                       mk uu____3415 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3515 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____3515
                    | FStar_Util.Inr c ->
                        let uu____3529 = close_comp cfg env c  in
                        FStar_Util.Inr uu____3529
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____3545 =
                    let uu____3546 =
                      let uu____3573 = closure_as_term_delayed cfg env t11
                         in
                      (uu____3573, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3546  in
                  mk uu____3545 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                  (match qi.FStar_Syntax_Syntax.qkind with
                   | FStar_Syntax_Syntax.Quote_dynamic  ->
                       let uu____3614 =
                         let uu____3615 =
                           let uu____3622 =
                             closure_as_term_delayed cfg env t'  in
                           (uu____3622, qi)  in
                         FStar_Syntax_Syntax.Tm_quoted uu____3615  in
                       mk uu____3614 t1.FStar_Syntax_Syntax.pos
                   | FStar_Syntax_Syntax.Quote_static  ->
                       let qi1 =
                         FStar_Syntax_Syntax.on_antiquoted
                           (closure_as_term_delayed cfg env) qi
                          in
                       mk (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3646 =
                    let uu____3647 =
                      let uu____3654 = closure_as_term_delayed cfg env t'  in
                      let uu____3657 =
                        let uu____3658 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____3658  in
                      (uu____3654, uu____3657)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3647  in
                  mk uu____3646 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3718 =
                    let uu____3719 =
                      let uu____3726 = closure_as_term_delayed cfg env t'  in
                      let uu____3729 =
                        let uu____3730 =
                          let uu____3737 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____3737)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____3730  in
                      (uu____3726, uu____3729)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3719  in
                  mk uu____3718 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3756 =
                    let uu____3757 =
                      let uu____3764 = closure_as_term_delayed cfg env t'  in
                      let uu____3767 =
                        let uu____3768 =
                          let uu____3777 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____3777)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3768  in
                      (uu____3764, uu____3767)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3757  in
                  mk uu____3756 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3790 =
                    let uu____3791 =
                      let uu____3798 = closure_as_term_delayed cfg env t'  in
                      (uu____3798, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3791  in
                  mk uu____3790 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3838  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____3857 =
                    let uu____3868 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____3868
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____3887 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___122_3899 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___122_3899.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___122_3899.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3887))
                     in
                  (match uu____3857 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___123_3915 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___123_3915.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___123_3915.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___123_3915.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___123_3915.FStar_Syntax_Syntax.lbpos)
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3926,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3985  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____4010 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4010
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____4030  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____4052 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4052
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___124_4064 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_4064.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_4064.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___125_4065 = lb  in
                    let uu____4066 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___125_4065.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___125_4065.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____4066;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___125_4065.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___125_4065.FStar_Syntax_Syntax.lbpos)
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4096  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____4185 =
                    match uu____4185 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4240 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4261 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4321  ->
                                        fun uu____4322  ->
                                          match (uu____4321, uu____4322) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4413 =
                                                norm_pat env3 p1  in
                                              (match uu____4413 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____4261 with
                               | (pats1,env3) ->
                                   ((let uu___126_4495 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___126_4495.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___127_4514 = x  in
                                let uu____4515 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___127_4514.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___127_4514.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4515
                                }  in
                              ((let uu___128_4529 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___128_4529.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___129_4540 = x  in
                                let uu____4541 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___129_4540.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___129_4540.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4541
                                }  in
                              ((let uu___130_4555 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___130_4555.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___131_4571 = x  in
                                let uu____4572 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___131_4571.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___131_4571.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4572
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___132_4579 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___132_4579.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____4582 = norm_pat env1 pat  in
                        (match uu____4582 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4611 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____4611
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____4617 =
                    let uu____4618 =
                      let uu____4641 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____4641)  in
                    FStar_Syntax_Syntax.Tm_match uu____4618  in
                  mk uu____4617 t1.FStar_Syntax_Syntax.pos))

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
        | uu____4727 -> closure_as_term cfg env t

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
        | uu____4753 ->
            FStar_List.map
              (fun uu____4770  ->
                 match uu____4770 with
                 | (x,imp) ->
                     let uu____4789 = closure_as_term_delayed cfg env x  in
                     (uu____4789, imp)) args

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
        let uu____4803 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4852  ->
                  fun uu____4853  ->
                    match (uu____4852, uu____4853) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___133_4923 = b  in
                          let uu____4924 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___133_4923.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___133_4923.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4924
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____4803 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____5017 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5030 = closure_as_term_delayed cfg env t  in
                 let uu____5031 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5030 uu____5031
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5044 = closure_as_term_delayed cfg env t  in
                 let uu____5045 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5044 uu____5045
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
                        (fun uu___80_5071  ->
                           match uu___80_5071 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5075 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____5075
                           | f -> f))
                    in
                 let uu____5079 =
                   let uu___134_5080 = c1  in
                   let uu____5081 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5081;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___134_5080.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5079)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___81_5091  ->
            match uu___81_5091 with
            | FStar_Syntax_Syntax.DECREASES uu____5092 -> false
            | uu____5095 -> true))

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
                   (fun uu___82_5113  ->
                      match uu___82_5113 with
                      | FStar_Syntax_Syntax.DECREASES uu____5114 -> false
                      | uu____5117 -> true))
               in
            let rc1 =
              let uu___135_5119 = rc  in
              let uu____5120 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___135_5119.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5120;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5127 -> lopt

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
    let uu____5212 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5212  in
  let arg_as_bounded_int uu____5240 =
    match uu____5240 with
    | (a,uu____5252) ->
        let uu____5259 =
          let uu____5260 = FStar_Syntax_Subst.compress a  in
          uu____5260.FStar_Syntax_Syntax.n  in
        (match uu____5259 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5270;
                FStar_Syntax_Syntax.vars = uu____5271;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5273;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5274;_},uu____5275)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____5314 =
               let uu____5319 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5319)  in
             FStar_Pervasives_Native.Some uu____5314
         | uu____5324 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5364 = f a  in FStar_Pervasives_Native.Some uu____5364
    | uu____5365 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5413 = f a0 a1  in FStar_Pervasives_Native.Some uu____5413
    | uu____5414 -> FStar_Pervasives_Native.None  in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5456 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a415  -> (Obj.magic (f res.psc_range)) a415)
                    uu____5456)) a416 a417 a418 a419 a420
     in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5505 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a421  ->
                       fun a422  -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____5505)) a423 a424 a425 a426 a427
     in
  let as_primitive_step is_strong uu____5532 =
    match uu____5532 with
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
    unary_op () (fun a428  -> (Obj.magic arg_as_int) a428)
      (fun a429  ->
         fun a430  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5580 = f x  in
                   FStar_Syntax_Embeddings.embed_int r uu____5580)) a429 a430)
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
                       let uu____5608 = f x y  in
                       FStar_Syntax_Embeddings.embed_int r uu____5608)) a432
               a433 a434)
     in
  let unary_bool_op f =
    unary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5629 = f x  in
                   FStar_Syntax_Embeddings.embed_bool r uu____5629)) a436
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
                       let uu____5657 = f x y  in
                       FStar_Syntax_Embeddings.embed_bool r uu____5657)) a439
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
                       let uu____5685 = f x y  in
                       FStar_Syntax_Embeddings.embed_string r uu____5685))
               a443 a444 a445)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____5793 =
          let uu____5802 = as_a a  in
          let uu____5805 = as_b b  in (uu____5802, uu____5805)  in
        (match uu____5793 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5820 =
               let uu____5821 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5821  in
             FStar_Pervasives_Native.Some uu____5820
         | uu____5822 -> FStar_Pervasives_Native.None)
    | uu____5831 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____5845 =
        let uu____5846 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5846  in
      mk uu____5845 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5856 =
      let uu____5859 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5859  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5856  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5891 =
      let uu____5892 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5892  in
    FStar_Syntax_Embeddings.embed_int rng uu____5891  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5910 = arg_as_string a1  in
        (match uu____5910 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5916 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2)
                in
             (match uu____5916 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5929 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5929
              | uu____5930 -> FStar_Pervasives_Native.None)
         | uu____5935 -> FStar_Pervasives_Native.None)
    | uu____5938 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5948 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____5948  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5977 =
          let uu____5998 = arg_as_string fn  in
          let uu____6001 = arg_as_int from_line  in
          let uu____6004 = arg_as_int from_col  in
          let uu____6007 = arg_as_int to_line  in
          let uu____6010 = arg_as_int to_col  in
          (uu____5998, uu____6001, uu____6004, uu____6007, uu____6010)  in
        (match uu____5977 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6041 =
                 let uu____6042 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6043 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6042 uu____6043  in
               let uu____6044 =
                 let uu____6045 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6046 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6045 uu____6046  in
               FStar_Range.mk_range fn1 uu____6041 uu____6044  in
             let uu____6047 =
               FStar_Syntax_Embeddings.embed_range psc.psc_range r  in
             FStar_Pervasives_Native.Some uu____6047
         | uu____6048 -> FStar_Pervasives_Native.None)
    | uu____6069 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6096)::(a1,uu____6098)::(a2,uu____6100)::[] ->
        let uu____6137 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6137 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6150 -> FStar_Pervasives_Native.None)
    | uu____6151 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____6178)::[] ->
        let uu____6187 = FStar_Syntax_Embeddings.unembed_range_safe a1  in
        (match uu____6187 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6193 =
               FStar_Syntax_Embeddings.embed_range psc.psc_range r  in
             FStar_Pervasives_Native.Some uu____6193
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6194 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6218 =
      let uu____6233 =
        let uu____6248 =
          let uu____6263 =
            let uu____6278 =
              let uu____6293 =
                let uu____6308 =
                  let uu____6323 =
                    let uu____6338 =
                      let uu____6353 =
                        let uu____6368 =
                          let uu____6383 =
                            let uu____6398 =
                              let uu____6413 =
                                let uu____6428 =
                                  let uu____6443 =
                                    let uu____6458 =
                                      let uu____6473 =
                                        let uu____6488 =
                                          let uu____6503 =
                                            let uu____6518 =
                                              let uu____6533 =
                                                let uu____6546 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____6546,
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
                                              let uu____6553 =
                                                let uu____6568 =
                                                  let uu____6581 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____6581,
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
                                                let uu____6588 =
                                                  let uu____6603 =
                                                    let uu____6618 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____6618,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____6627 =
                                                    let uu____6644 =
                                                      let uu____6659 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____6659,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____6644]  in
                                                  uu____6603 :: uu____6627
                                                   in
                                                uu____6568 :: uu____6588  in
                                              uu____6533 :: uu____6553  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6518
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6503
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
                                          :: uu____6488
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
                                        :: uu____6473
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
                                      :: uu____6458
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
                                                        let uu____6850 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____6850 y)) a466
                                                a467 a468)))
                                    :: uu____6443
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6428
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6413
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6398
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6383
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6368
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6353
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
                                          let uu____7017 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____7017)) a470 a471 a472)))
                      :: uu____6338
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
                                        let uu____7043 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____7043)) a474 a475 a476)))
                    :: uu____6323
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
                                      let uu____7069 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____7069)) a478 a479 a480)))
                  :: uu____6308
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
                                    let uu____7095 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____7095)) a482 a483 a484)))
                :: uu____6293
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6278
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6263
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6248
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6233
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6218
     in
  let weak_ops =
    let uu____7234 =
      let uu____7253 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____7253, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____7234]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7337 =
        let uu____7338 =
          let uu____7339 = FStar_Syntax_Syntax.as_arg c  in [uu____7339]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7338  in
      uu____7337 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7389 =
                let uu____7402 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7402, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486  ->
                        fun a487  ->
                          fun a488  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7418  ->
                                    fun uu____7419  ->
                                      match (uu____7418, uu____7419) with
                                      | ((int_to_t1,x),(uu____7438,y)) ->
                                          let uu____7448 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7448)) a486 a487 a488)))
                 in
              let uu____7449 =
                let uu____7464 =
                  let uu____7477 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7477, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490  ->
                          fun a491  ->
                            fun a492  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7493  ->
                                      fun uu____7494  ->
                                        match (uu____7493, uu____7494) with
                                        | ((int_to_t1,x),(uu____7513,y)) ->
                                            let uu____7523 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7523)) a490 a491 a492)))
                   in
                let uu____7524 =
                  let uu____7539 =
                    let uu____7552 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____7552, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494  ->
                            fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7568  ->
                                        fun uu____7569  ->
                                          match (uu____7568, uu____7569) with
                                          | ((int_to_t1,x),(uu____7588,y)) ->
                                              let uu____7598 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____7598)) a494 a495 a496)))
                     in
                  let uu____7599 =
                    let uu____7614 =
                      let uu____7627 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____7627, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498  ->
                              fun a499  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7639  ->
                                        match uu____7639 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499)))
                       in
                    [uu____7614]  in
                  uu____7539 :: uu____7599  in
                uu____7464 :: uu____7524  in
              uu____7389 :: uu____7449))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____7753 =
                let uu____7766 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____7766, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500  -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501  ->
                        fun a502  ->
                          fun a503  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7782  ->
                                    fun uu____7783  ->
                                      match (uu____7782, uu____7783) with
                                      | ((int_to_t1,x),(uu____7802,y)) ->
                                          let uu____7812 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7812)) a501 a502 a503)))
                 in
              let uu____7813 =
                let uu____7828 =
                  let uu____7841 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____7841, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504  -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505  ->
                          fun a506  ->
                            fun a507  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7857  ->
                                      fun uu____7858  ->
                                        match (uu____7857, uu____7858) with
                                        | ((int_to_t1,x),(uu____7877,y)) ->
                                            let uu____7887 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7887)) a505 a506 a507)))
                   in
                [uu____7828]  in
              uu____7753 :: uu____7813))
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
    | (_typ,uu____7999)::(a1,uu____8001)::(a2,uu____8003)::[] ->
        let uu____8040 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8040 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___136_8046 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___136_8046.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___136_8046.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___137_8050 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___137_8050.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___137_8050.FStar_Syntax_Syntax.vars)
                })
         | uu____8051 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8053)::uu____8054::(a1,uu____8056)::(a2,uu____8058)::[] ->
        let uu____8107 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8107 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___136_8113 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___136_8113.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___136_8113.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___137_8117 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___137_8117.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___137_8117.FStar_Syntax_Syntax.vars)
                })
         | uu____8118 -> FStar_Pervasives_Native.None)
    | uu____8119 -> failwith "Unexpected number of arguments"  in
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
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.unembedder
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____8171 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____8171 with
    | FStar_Pervasives_Native.Some f -> f t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____8218 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8218) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8278  ->
           fun subst1  ->
             match uu____8278 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8319,uu____8320)) ->
                      let uu____8379 = b  in
                      (match uu____8379 with
                       | (bv,uu____8387) ->
                           let uu____8388 =
                             let uu____8389 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____8389  in
                           if uu____8388
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8394 = unembed_binder term1  in
                              match uu____8394 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8401 =
                                      let uu___138_8402 = bv  in
                                      let uu____8403 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___138_8402.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___138_8402.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8403
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8401
                                     in
                                  let b_for_x =
                                    let uu____8407 =
                                      let uu____8414 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8414)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8407  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___83_8423  ->
                                         match uu___83_8423 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8424,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8426;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8427;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____8432 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8433 -> subst1)) env []
  
let reduce_primops :
  'Auu____8450 'Auu____8451 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8450) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8451 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8493 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8493 with
             | (head1,args) ->
                 let uu____8530 =
                   let uu____8531 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8531.FStar_Syntax_Syntax.n  in
                 (match uu____8530 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8535 = find_prim_step cfg fv  in
                      (match uu____8535 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8550  ->
                                   let uu____8551 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____8552 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args)
                                      in
                                   let uu____8559 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8551 uu____8552 uu____8559);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____8564  ->
                                   let uu____8565 =
                                     FStar_Syntax_Print.term_to_string tm  in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____8565);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____8568  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 }  in
                               let uu____8570 =
                                 prim_step.interpretation psc args  in
                               match uu____8570 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____8576  ->
                                         let uu____8577 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____8577);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____8583  ->
                                         let uu____8584 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         let uu____8585 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced
                                            in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____8584 uu____8585);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____8586 ->
                           (log_primops cfg
                              (fun uu____8590  ->
                                 let uu____8591 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8591);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8595  ->
                            let uu____8596 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8596);
                       (match args with
                        | (a1,uu____8598)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8615 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8627  ->
                            let uu____8628 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8628);
                       (match args with
                        | (t,uu____8630)::(r,uu____8632)::[] ->
                            let uu____8659 =
                              FStar_Syntax_Embeddings.unembed_range r  in
                            (match uu____8659 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___139_8663 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___139_8663.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___139_8663.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____8666 -> tm))
                  | uu____8675 -> tm))
  
let reduce_equality :
  'Auu____8680 'Auu____8681 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8680) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8681 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___140_8719 = cfg  in
         {
           steps =
             (let uu___141_8722 = default_steps  in
              {
                beta = (uu___141_8722.beta);
                iota = (uu___141_8722.iota);
                zeta = (uu___141_8722.zeta);
                weak = (uu___141_8722.weak);
                hnf = (uu___141_8722.hnf);
                primops = true;
                no_delta_steps = (uu___141_8722.no_delta_steps);
                unfold_until = (uu___141_8722.unfold_until);
                unfold_only = (uu___141_8722.unfold_only);
                unfold_attr = (uu___141_8722.unfold_attr);
                unfold_tac = (uu___141_8722.unfold_tac);
                pure_subterms_within_computations =
                  (uu___141_8722.pure_subterms_within_computations);
                simplify = (uu___141_8722.simplify);
                erase_universes = (uu___141_8722.erase_universes);
                allow_unbound_universes =
                  (uu___141_8722.allow_unbound_universes);
                reify_ = (uu___141_8722.reify_);
                compress_uvars = (uu___141_8722.compress_uvars);
                no_full_norm = (uu___141_8722.no_full_norm);
                check_no_uvars = (uu___141_8722.check_no_uvars);
                unmeta = (uu___141_8722.unmeta);
                unascribe = (uu___141_8722.unascribe)
              });
           tcenv = (uu___140_8719.tcenv);
           debug = (uu___140_8719.debug);
           delta_level = (uu___140_8719.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___140_8719.strong);
           memoize_lazy = (uu___140_8719.memoize_lazy);
           normalize_pure_lets = (uu___140_8719.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____8726 .
    FStar_Syntax_Syntax.term -> 'Auu____8726 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____8739 =
        let uu____8746 =
          let uu____8747 = FStar_Syntax_Util.un_uinst hd1  in
          uu____8747.FStar_Syntax_Syntax.n  in
        (uu____8746, args)  in
      match uu____8739 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____8753::uu____8754::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____8758::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____8763::uu____8764::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____8767 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___84_8778  ->
    match uu___84_8778 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____8784 =
          let uu____8787 =
            let uu____8788 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldOnly uu____8788  in
          [uu____8787]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____8784
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____8804 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____8804) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        try
          let uu____8857 =
            let uu____8860 =
              let uu____8863 =
                let uu____8868 =
                  FStar_Syntax_Embeddings.unembed_list_safe
                    FStar_Syntax_Embeddings.unembed_norm_step
                   in
                uu____8868 s  in
              FStar_All.pipe_right uu____8863 FStar_Util.must  in
            FStar_All.pipe_right uu____8860 tr_norm_steps  in
          FStar_Pervasives_Native.Some uu____8857
        with | uu____8896 -> FStar_Pervasives_Native.None  in
      match args with
      | uu____8907::(tm,uu____8909)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____8938)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____8959)::uu____8960::(tm,uu____8962)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____8999 =
            let uu____9004 = full_norm steps  in parse_steps uu____9004  in
          (match uu____8999 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____9043 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___85_9060  ->
    match uu___85_9060 with
    | (App
        (uu____9063,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____9064;
                      FStar_Syntax_Syntax.vars = uu____9065;_},uu____9066,uu____9067))::uu____9068
        -> true
    | uu____9075 -> false
  
let firstn :
  'Auu____9081 .
    Prims.int ->
      'Auu____9081 Prims.list ->
        ('Auu____9081 Prims.list,'Auu____9081 Prims.list)
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
          (uu____9117,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____9118;
                        FStar_Syntax_Syntax.vars = uu____9119;_},uu____9120,uu____9121))::uu____9122
          -> (cfg.steps).reify_
      | uu____9129 -> false
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9313 ->
                   let uu____9338 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9338
               | uu____9339 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____9347  ->
               let uu____9348 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9349 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9350 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9357 =
                 let uu____9358 =
                   let uu____9361 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9361
                    in
                 stack_to_string uu____9358  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____9348 uu____9349 uu____9350 uu____9357);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____9384 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____9385 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____9386 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9387;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____9388;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9391;
                 FStar_Syntax_Syntax.fv_delta = uu____9392;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9393;
                 FStar_Syntax_Syntax.fv_delta = uu____9394;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9395);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____9402 ->
               rebuild cfg env stack t1
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
                 let uu___144_9438 = cfg  in
                 {
                   steps =
                     (let uu___145_9441 = cfg.steps  in
                      {
                        beta = (uu___145_9441.beta);
                        iota = (uu___145_9441.iota);
                        zeta = (uu___145_9441.zeta);
                        weak = (uu___145_9441.weak);
                        hnf = (uu___145_9441.hnf);
                        primops = (uu___145_9441.primops);
                        no_delta_steps = false;
                        unfold_until = (uu___145_9441.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___145_9441.unfold_attr);
                        unfold_tac = (uu___145_9441.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___145_9441.pure_subterms_within_computations);
                        simplify = (uu___145_9441.simplify);
                        erase_universes = (uu___145_9441.erase_universes);
                        allow_unbound_universes =
                          (uu___145_9441.allow_unbound_universes);
                        reify_ = (uu___145_9441.reify_);
                        compress_uvars = (uu___145_9441.compress_uvars);
                        no_full_norm = (uu___145_9441.no_full_norm);
                        check_no_uvars = (uu___145_9441.check_no_uvars);
                        unmeta = (uu___145_9441.unmeta);
                        unascribe = (uu___145_9441.unascribe)
                      });
                   tcenv = (uu___144_9438.tcenv);
                   debug = (uu___144_9438.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___144_9438.primitive_steps);
                   strong = (uu___144_9438.strong);
                   memoize_lazy = (uu___144_9438.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____9444 = get_norm_request (norm cfg' env []) args  in
               (match uu____9444 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____9475  ->
                              fun stack1  ->
                                match uu____9475 with
                                | (a,aq) ->
                                    let uu____9487 =
                                      let uu____9488 =
                                        let uu____9495 =
                                          let uu____9496 =
                                            let uu____9527 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____9527, false)  in
                                          Clos uu____9496  in
                                        (uu____9495, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____9488  in
                                    uu____9487 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____9611  ->
                          let uu____9612 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____9612);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____9634 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___86_9639  ->
                                match uu___86_9639 with
                                | UnfoldUntil uu____9640 -> true
                                | UnfoldOnly uu____9641 -> true
                                | uu____9644 -> false))
                         in
                      if uu____9634
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___146_9649 = cfg  in
                      let uu____9650 = to_fsteps s  in
                      {
                        steps = uu____9650;
                        tcenv = (uu___146_9649.tcenv);
                        debug = (uu___146_9649.debug);
                        delta_level;
                        primitive_steps = (uu___146_9649.primitive_steps);
                        strong = (uu___146_9649.strong);
                        memoize_lazy = (uu___146_9649.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____9659 =
                          let uu____9660 =
                            let uu____9665 = FStar_Util.now ()  in
                            (t1, uu____9665)  in
                          Debug uu____9660  in
                        uu____9659 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____9669 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____9669
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____9678 =
                      let uu____9685 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____9685, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____9678  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____9695 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____9695  in
               let uu____9696 = FStar_TypeChecker_Env.qninfo_is_action qninfo
                  in
               if uu____9696
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____9702  ->
                       let uu____9703 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____9704 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____9703 uu____9704);
                  if b
                  then
                    (let uu____9705 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____9705 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    (let uu____9713 = find_prim_step cfg fv  in
                     FStar_Option.isNone uu____9713) &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___87_9719  ->
                               match uu___87_9719 with
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
                          (let uu____9729 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____9729))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____9748) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____9783,uu____9784) -> false)))
                     in
                  log cfg
                    (fun uu____9806  ->
                       let uu____9807 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____9808 =
                         FStar_Range.string_of_range
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____9809 =
                         FStar_Util.string_of_bool should_delta1  in
                       FStar_Util.print3
                         ">>> For %s (%s), should_delta = %s\n" uu____9807
                         uu____9808 uu____9809);
                  if should_delta1
                  then do_unfold_fv cfg env stack t1 qninfo fv
                  else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____9812 = lookup_bvar env x  in
               (match uu____9812 with
                | Univ uu____9815 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____9864 = FStar_ST.op_Bang r  in
                      (match uu____9864 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____9982  ->
                                 let uu____9983 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____9984 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____9983
                                   uu____9984);
                            (let uu____9985 =
                               let uu____9986 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____9986.FStar_Syntax_Syntax.n  in
                             match uu____9985 with
                             | FStar_Syntax_Syntax.Tm_abs uu____9989 ->
                                 norm cfg env2 stack t'
                             | uu____10006 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10076)::uu____10077 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____10086)::uu____10087 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____10097,uu____10098))::stack_rest ->
                    (match c with
                     | Univ uu____10102 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10111 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____10132  ->
                                    let uu____10133 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10133);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____10173  ->
                                    let uu____10174 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10174);
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
                       (fun uu____10252  ->
                          let uu____10253 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10253);
                     norm cfg env stack1 t1)
                | (Debug uu____10254)::uu____10255 ->
                    if (cfg.steps).weak
                    then
                      let uu____10262 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10262
                    else
                      (let uu____10264 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10264 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10306  -> dummy :: env1) env)
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
                                          let uu____10343 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10343)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___147_10348 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___147_10348.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___147_10348.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10349 -> lopt  in
                           (log cfg
                              (fun uu____10355  ->
                                 let uu____10356 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10356);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___148_10365 = cfg  in
                               {
                                 steps = (uu___148_10365.steps);
                                 tcenv = (uu___148_10365.tcenv);
                                 debug = (uu___148_10365.debug);
                                 delta_level = (uu___148_10365.delta_level);
                                 primitive_steps =
                                   (uu___148_10365.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___148_10365.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___148_10365.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10376)::uu____10377 ->
                    if (cfg.steps).weak
                    then
                      let uu____10384 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10384
                    else
                      (let uu____10386 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10386 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10428  -> dummy :: env1) env)
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
                                          let uu____10465 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10465)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___147_10470 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___147_10470.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___147_10470.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10471 -> lopt  in
                           (log cfg
                              (fun uu____10477  ->
                                 let uu____10478 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10478);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___148_10487 = cfg  in
                               {
                                 steps = (uu___148_10487.steps);
                                 tcenv = (uu___148_10487.tcenv);
                                 debug = (uu___148_10487.debug);
                                 delta_level = (uu___148_10487.delta_level);
                                 primitive_steps =
                                   (uu___148_10487.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___148_10487.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___148_10487.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____10498)::uu____10499 ->
                    if (cfg.steps).weak
                    then
                      let uu____10510 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10510
                    else
                      (let uu____10512 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10512 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10554  -> dummy :: env1) env)
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
                                          let uu____10591 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10591)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___147_10596 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___147_10596.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___147_10596.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10597 -> lopt  in
                           (log cfg
                              (fun uu____10603  ->
                                 let uu____10604 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10604);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___148_10613 = cfg  in
                               {
                                 steps = (uu___148_10613.steps);
                                 tcenv = (uu___148_10613.tcenv);
                                 debug = (uu___148_10613.debug);
                                 delta_level = (uu___148_10613.delta_level);
                                 primitive_steps =
                                   (uu___148_10613.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___148_10613.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___148_10613.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____10624)::uu____10625 ->
                    if (cfg.steps).weak
                    then
                      let uu____10636 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10636
                    else
                      (let uu____10638 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10638 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10680  -> dummy :: env1) env)
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
                                          let uu____10717 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10717)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___147_10722 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___147_10722.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___147_10722.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10723 -> lopt  in
                           (log cfg
                              (fun uu____10729  ->
                                 let uu____10730 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10730);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___148_10739 = cfg  in
                               {
                                 steps = (uu___148_10739.steps);
                                 tcenv = (uu___148_10739.tcenv);
                                 debug = (uu___148_10739.debug);
                                 delta_level = (uu___148_10739.delta_level);
                                 primitive_steps =
                                   (uu___148_10739.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___148_10739.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___148_10739.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____10750)::uu____10751 ->
                    if (cfg.steps).weak
                    then
                      let uu____10766 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10766
                    else
                      (let uu____10768 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10768 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10810  -> dummy :: env1) env)
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
                                          let uu____10847 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10847)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___147_10852 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___147_10852.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___147_10852.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10853 -> lopt  in
                           (log cfg
                              (fun uu____10859  ->
                                 let uu____10860 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10860);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___148_10869 = cfg  in
                               {
                                 steps = (uu___148_10869.steps);
                                 tcenv = (uu___148_10869.tcenv);
                                 debug = (uu___148_10869.debug);
                                 delta_level = (uu___148_10869.delta_level);
                                 primitive_steps =
                                   (uu___148_10869.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___148_10869.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___148_10869.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____10880 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10880
                    else
                      (let uu____10882 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10882 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10924  -> dummy :: env1) env)
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
                                          let uu____10961 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10961)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___147_10966 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___147_10966.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___147_10966.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10967 -> lopt  in
                           (log cfg
                              (fun uu____10973  ->
                                 let uu____10974 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10974);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___148_10983 = cfg  in
                               {
                                 steps = (uu___148_10983.steps);
                                 tcenv = (uu___148_10983.tcenv);
                                 debug = (uu___148_10983.debug);
                                 delta_level = (uu___148_10983.delta_level);
                                 primitive_steps =
                                   (uu___148_10983.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___148_10983.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___148_10983.normalize_pure_lets)
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
                      (fun uu____11032  ->
                         fun stack1  ->
                           match uu____11032 with
                           | (a,aq) ->
                               let uu____11044 =
                                 let uu____11045 =
                                   let uu____11052 =
                                     let uu____11053 =
                                       let uu____11084 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____11084, false)  in
                                     Clos uu____11053  in
                                   (uu____11052, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____11045  in
                               uu____11044 :: stack1) args)
                  in
               (log cfg
                  (fun uu____11168  ->
                     let uu____11169 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____11169);
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
                             ((let uu___149_11205 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___149_11205.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___149_11205.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____11206 ->
                      let uu____11211 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11211)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____11214 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____11214 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____11245 =
                          let uu____11246 =
                            let uu____11253 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___150_11255 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___150_11255.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___150_11255.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____11253)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____11246  in
                        mk uu____11245 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____11274 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____11274
               else
                 (let uu____11276 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____11276 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____11284 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____11308  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____11284 c1  in
                      let t2 =
                        let uu____11330 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____11330 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____11441)::uu____11442 ->
                    (log cfg
                       (fun uu____11453  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____11454)::uu____11455 ->
                    (log cfg
                       (fun uu____11466  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____11467,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____11468;
                                   FStar_Syntax_Syntax.vars = uu____11469;_},uu____11470,uu____11471))::uu____11472
                    ->
                    (log cfg
                       (fun uu____11481  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____11482)::uu____11483 ->
                    (log cfg
                       (fun uu____11494  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____11495 ->
                    (log cfg
                       (fun uu____11498  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____11502  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____11519 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____11519
                         | FStar_Util.Inr c ->
                             let uu____11527 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____11527
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____11540 =
                               let uu____11541 =
                                 let uu____11568 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____11568, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11541
                                in
                             mk uu____11540 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____11587 ->
                           let uu____11588 =
                             let uu____11589 =
                               let uu____11590 =
                                 let uu____11617 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____11617, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11590
                                in
                             mk uu____11589 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____11588))))
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
                         let uu____11727 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____11727 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___151_11747 = cfg  in
                               let uu____11748 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___151_11747.steps);
                                 tcenv = uu____11748;
                                 debug = (uu___151_11747.debug);
                                 delta_level = (uu___151_11747.delta_level);
                                 primitive_steps =
                                   (uu___151_11747.primitive_steps);
                                 strong = (uu___151_11747.strong);
                                 memoize_lazy = (uu___151_11747.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11747.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____11753 =
                                 let uu____11754 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____11754  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____11753
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___152_11757 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___152_11757.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___152_11757.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___152_11757.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___152_11757.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____11758 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____11758
           | FStar_Syntax_Syntax.Tm_let
               ((uu____11769,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____11770;
                               FStar_Syntax_Syntax.lbunivs = uu____11771;
                               FStar_Syntax_Syntax.lbtyp = uu____11772;
                               FStar_Syntax_Syntax.lbeff = uu____11773;
                               FStar_Syntax_Syntax.lbdef = uu____11774;
                               FStar_Syntax_Syntax.lbattrs = uu____11775;
                               FStar_Syntax_Syntax.lbpos = uu____11776;_}::uu____11777),uu____11778)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____11818 =
                 (Prims.op_Negation (cfg.steps).no_delta_steps) &&
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
               if uu____11818
               then
                 let binder =
                   let uu____11820 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____11820  in
                 let env1 =
                   let uu____11830 =
                     let uu____11837 =
                       let uu____11838 =
                         let uu____11869 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____11869,
                           false)
                          in
                       Clos uu____11838  in
                     ((FStar_Pervasives_Native.Some binder), uu____11837)  in
                   uu____11830 :: env  in
                 (log cfg
                    (fun uu____11962  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____11966  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____11967 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____11967))
                 else
                   (let uu____11969 =
                      let uu____11974 =
                        let uu____11975 =
                          let uu____11976 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____11976
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____11975]  in
                      FStar_Syntax_Subst.open_term uu____11974 body  in
                    match uu____11969 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____11985  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____11993 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____11993  in
                            FStar_Util.Inl
                              (let uu___153_12003 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___153_12003.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___153_12003.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____12006  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___154_12008 = lb  in
                             let uu____12009 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___154_12008.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___154_12008.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____12009;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___154_12008.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___154_12008.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12044  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___155_12067 = cfg  in
                             {
                               steps = (uu___155_12067.steps);
                               tcenv = (uu___155_12067.tcenv);
                               debug = (uu___155_12067.debug);
                               delta_level = (uu___155_12067.delta_level);
                               primitive_steps =
                                 (uu___155_12067.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___155_12067.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___155_12067.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____12070  ->
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
               let uu____12087 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____12087 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____12123 =
                               let uu___156_12124 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___156_12124.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___156_12124.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____12123  in
                           let uu____12125 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____12125 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____12151 =
                                   FStar_List.map (fun uu____12167  -> dummy)
                                     lbs1
                                    in
                                 let uu____12168 =
                                   let uu____12177 =
                                     FStar_List.map
                                       (fun uu____12197  -> dummy) xs1
                                      in
                                   FStar_List.append uu____12177 env  in
                                 FStar_List.append uu____12151 uu____12168
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12221 =
                                       let uu___157_12222 = rc  in
                                       let uu____12223 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___157_12222.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12223;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___157_12222.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____12221
                                 | uu____12230 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___158_12234 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___158_12234.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___158_12234.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___158_12234.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___158_12234.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____12244 =
                        FStar_List.map (fun uu____12260  -> dummy) lbs2  in
                      FStar_List.append uu____12244 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____12268 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____12268 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___159_12284 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___159_12284.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___159_12284.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____12311 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____12311
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____12330 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____12406  ->
                        match uu____12406 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___160_12527 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___160_12527.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___160_12527.FStar_Syntax_Syntax.sort)
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
               (match uu____12330 with
                | (rec_env,memos,uu____12740) ->
                    let uu____12793 =
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
                             let uu____13104 =
                               let uu____13111 =
                                 let uu____13112 =
                                   let uu____13143 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____13143, false)
                                    in
                                 Clos uu____13112  in
                               (FStar_Pervasives_Native.None, uu____13111)
                                in
                             uu____13104 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____13253  ->
                     let uu____13254 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____13254);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____13276 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____13278::uu____13279 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____13284) ->
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
                             | uu____13307 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____13321 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____13321
                              | uu____13332 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____13336 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____13362 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____13380 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____13397 =
                        let uu____13398 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____13399 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____13398 uu____13399
                         in
                      failwith uu____13397
                    else rebuild cfg env stack t2
                | uu____13401 -> norm cfg env stack t2))

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
                let uu____13411 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____13411  in
              let uu____13412 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____13412 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____13425  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____13436  ->
                        let uu____13437 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____13438 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____13437 uu____13438);
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
                      | (UnivArgs (us',uu____13451))::stack1 ->
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
                      | uu____13506 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____13509 ->
                          let uu____13512 =
                            let uu____13513 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____13513
                             in
                          failwith uu____13512
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
                  let uu___161_13537 = cfg  in
                  let uu____13538 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____13538;
                    tcenv = (uu___161_13537.tcenv);
                    debug = (uu___161_13537.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___161_13537.primitive_steps);
                    strong = (uu___161_13537.strong);
                    memoize_lazy = (uu___161_13537.memoize_lazy);
                    normalize_pure_lets =
                      (uu___161_13537.normalize_pure_lets)
                  }
                else
                  (let uu___162_13540 = cfg  in
                   {
                     steps =
                       (let uu___163_13543 = cfg.steps  in
                        {
                          beta = (uu___163_13543.beta);
                          iota = (uu___163_13543.iota);
                          zeta = false;
                          weak = (uu___163_13543.weak);
                          hnf = (uu___163_13543.hnf);
                          primops = (uu___163_13543.primops);
                          no_delta_steps = (uu___163_13543.no_delta_steps);
                          unfold_until = (uu___163_13543.unfold_until);
                          unfold_only = (uu___163_13543.unfold_only);
                          unfold_attr = (uu___163_13543.unfold_attr);
                          unfold_tac = (uu___163_13543.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___163_13543.pure_subterms_within_computations);
                          simplify = (uu___163_13543.simplify);
                          erase_universes = (uu___163_13543.erase_universes);
                          allow_unbound_universes =
                            (uu___163_13543.allow_unbound_universes);
                          reify_ = (uu___163_13543.reify_);
                          compress_uvars = (uu___163_13543.compress_uvars);
                          no_full_norm = (uu___163_13543.no_full_norm);
                          check_no_uvars = (uu___163_13543.check_no_uvars);
                          unmeta = (uu___163_13543.unmeta);
                          unascribe = (uu___163_13543.unascribe)
                        });
                     tcenv = (uu___162_13540.tcenv);
                     debug = (uu___162_13540.debug);
                     delta_level = (uu___162_13540.delta_level);
                     primitive_steps = (uu___162_13540.primitive_steps);
                     strong = (uu___162_13540.strong);
                     memoize_lazy = (uu___162_13540.memoize_lazy);
                     normalize_pure_lets =
                       (uu___162_13540.normalize_pure_lets)
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
                  (fun uu____13573  ->
                     let uu____13574 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____13575 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____13574
                       uu____13575);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____13577 =
                   let uu____13578 = FStar_Syntax_Subst.compress head3  in
                   uu____13578.FStar_Syntax_Syntax.n  in
                 match uu____13577 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____13596 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____13596
                        in
                     let uu____13597 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____13597 with
                      | (uu____13598,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____13604 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____13612 =
                                   let uu____13613 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____13613.FStar_Syntax_Syntax.n  in
                                 match uu____13612 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____13619,uu____13620))
                                     ->
                                     let uu____13629 =
                                       let uu____13630 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____13630.FStar_Syntax_Syntax.n  in
                                     (match uu____13629 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____13636,msrc,uu____13638))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____13647 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13647
                                      | uu____13648 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____13649 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____13650 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____13650 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___164_13655 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___164_13655.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___164_13655.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___164_13655.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___164_13655.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___164_13655.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____13656 = FStar_List.tl stack  in
                                    let uu____13657 =
                                      let uu____13658 =
                                        let uu____13661 =
                                          let uu____13662 =
                                            let uu____13675 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____13675)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____13662
                                           in
                                        FStar_Syntax_Syntax.mk uu____13661
                                         in
                                      uu____13658
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____13656 uu____13657
                                | FStar_Pervasives_Native.None  ->
                                    let uu____13691 =
                                      let uu____13692 = is_return body  in
                                      match uu____13692 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____13696;
                                            FStar_Syntax_Syntax.vars =
                                              uu____13697;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____13702 -> false  in
                                    if uu____13691
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
                                         let uu____13725 =
                                           let uu____13728 =
                                             let uu____13729 =
                                               let uu____13746 =
                                                 let uu____13749 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____13749]  in
                                               (uu____13746, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____13729
                                              in
                                           FStar_Syntax_Syntax.mk uu____13728
                                            in
                                         uu____13725
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____13765 =
                                           let uu____13766 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____13766.FStar_Syntax_Syntax.n
                                            in
                                         match uu____13765 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____13772::uu____13773::[])
                                             ->
                                             let uu____13780 =
                                               let uu____13783 =
                                                 let uu____13784 =
                                                   let uu____13791 =
                                                     let uu____13794 =
                                                       let uu____13795 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____13795
                                                        in
                                                     let uu____13796 =
                                                       let uu____13799 =
                                                         let uu____13800 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____13800
                                                          in
                                                       [uu____13799]  in
                                                     uu____13794 ::
                                                       uu____13796
                                                      in
                                                   (bind1, uu____13791)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____13784
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____13783
                                                in
                                             uu____13780
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____13808 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____13814 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____13814
                                         then
                                           let uu____13817 =
                                             let uu____13818 =
                                               FStar_Syntax_Embeddings.embed_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____13818
                                              in
                                           let uu____13819 =
                                             let uu____13822 =
                                               let uu____13823 =
                                                 FStar_Syntax_Embeddings.embed_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____13823
                                                in
                                             [uu____13822]  in
                                           uu____13817 :: uu____13819
                                         else []  in
                                       let reified =
                                         let uu____13828 =
                                           let uu____13831 =
                                             let uu____13832 =
                                               let uu____13847 =
                                                 let uu____13850 =
                                                   let uu____13853 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____13854 =
                                                     let uu____13857 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____13857]  in
                                                   uu____13853 :: uu____13854
                                                    in
                                                 let uu____13858 =
                                                   let uu____13861 =
                                                     let uu____13864 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____13865 =
                                                       let uu____13868 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____13869 =
                                                         let uu____13872 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____13873 =
                                                           let uu____13876 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____13876]  in
                                                         uu____13872 ::
                                                           uu____13873
                                                          in
                                                       uu____13868 ::
                                                         uu____13869
                                                        in
                                                     uu____13864 ::
                                                       uu____13865
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____13861
                                                    in
                                                 FStar_List.append
                                                   uu____13850 uu____13858
                                                  in
                                               (bind_inst, uu____13847)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____13832
                                              in
                                           FStar_Syntax_Syntax.mk uu____13831
                                            in
                                         uu____13828
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____13888  ->
                                            let uu____13889 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____13890 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____13889 uu____13890);
                                       (let uu____13891 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____13891 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____13915 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____13915
                        in
                     let uu____13916 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____13916 with
                      | (uu____13917,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____13952 =
                                  let uu____13953 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____13953.FStar_Syntax_Syntax.n  in
                                match uu____13952 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____13959) -> t2
                                | uu____13964 -> head4  in
                              let uu____13965 =
                                let uu____13966 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____13966.FStar_Syntax_Syntax.n  in
                              match uu____13965 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____13972 -> FStar_Pervasives_Native.None
                               in
                            let uu____13973 = maybe_extract_fv head4  in
                            match uu____13973 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____13983 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____13983
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____13988 = maybe_extract_fv head5
                                     in
                                  match uu____13988 with
                                  | FStar_Pervasives_Native.Some uu____13993
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____13994 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____13999 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____14014 =
                              match uu____14014 with
                              | (e,q) ->
                                  let uu____14021 =
                                    let uu____14022 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14022.FStar_Syntax_Syntax.n  in
                                  (match uu____14021 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____14037 -> false)
                               in
                            let uu____14038 =
                              let uu____14039 =
                                let uu____14046 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____14046 :: args  in
                              FStar_Util.for_some is_arg_impure uu____14039
                               in
                            if uu____14038
                            then
                              let uu____14051 =
                                let uu____14052 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____14052
                                 in
                              failwith uu____14051
                            else ());
                           (let uu____14054 = maybe_unfold_action head_app
                               in
                            match uu____14054 with
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
                                   (fun uu____14095  ->
                                      let uu____14096 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____14097 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____14096 uu____14097);
                                 (let uu____14098 = FStar_List.tl stack  in
                                  norm cfg env uu____14098 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____14100) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____14124 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____14124  in
                     (log cfg
                        (fun uu____14128  ->
                           let uu____14129 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____14129);
                      (let uu____14130 = FStar_List.tl stack  in
                       norm cfg env uu____14130 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____14251  ->
                               match uu____14251 with
                               | (pat,wopt,tm) ->
                                   let uu____14299 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____14299)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____14331 = FStar_List.tl stack  in
                     norm cfg env uu____14331 tm
                 | uu____14332 -> fallback ())

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
              (fun uu____14346  ->
                 let uu____14347 = FStar_Ident.string_of_lid msrc  in
                 let uu____14348 = FStar_Ident.string_of_lid mtgt  in
                 let uu____14349 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____14347
                   uu____14348 uu____14349);
            if
              (FStar_Syntax_Util.is_pure_effect msrc) ||
                (FStar_Syntax_Util.is_div_effect msrc)
            then
              (let ed =
                 let uu____14351 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____14351  in
               let uu____14352 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____14352 with
               | (uu____14353,return_repr) ->
                   let return_inst =
                     let uu____14362 =
                       let uu____14363 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____14363.FStar_Syntax_Syntax.n  in
                     match uu____14362 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____14369::[]) ->
                         let uu____14376 =
                           let uu____14379 =
                             let uu____14380 =
                               let uu____14387 =
                                 let uu____14390 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____14390]  in
                               (return_tm, uu____14387)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____14380  in
                           FStar_Syntax_Syntax.mk uu____14379  in
                         uu____14376 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____14398 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____14401 =
                     let uu____14404 =
                       let uu____14405 =
                         let uu____14420 =
                           let uu____14423 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____14424 =
                             let uu____14427 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____14427]  in
                           uu____14423 :: uu____14424  in
                         (return_inst, uu____14420)  in
                       FStar_Syntax_Syntax.Tm_app uu____14405  in
                     FStar_Syntax_Syntax.mk uu____14404  in
                   uu____14401 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____14436 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____14436 with
               | FStar_Pervasives_Native.None  ->
                   let uu____14439 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____14439
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14440;
                     FStar_TypeChecker_Env.mtarget = uu____14441;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14442;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____14457 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____14457
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____14458;
                     FStar_TypeChecker_Env.mtarget = uu____14459;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____14460;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____14484 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____14485 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____14484 t FStar_Syntax_Syntax.tun uu____14485)

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
                (fun uu____14541  ->
                   match uu____14541 with
                   | (a,imp) ->
                       let uu____14552 = norm cfg env [] a  in
                       (uu____14552, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___165_14566 = comp  in
            let uu____14567 =
              let uu____14568 =
                let uu____14577 = norm cfg env [] t  in
                let uu____14578 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____14577, uu____14578)  in
              FStar_Syntax_Syntax.Total uu____14568  in
            {
              FStar_Syntax_Syntax.n = uu____14567;
              FStar_Syntax_Syntax.pos =
                (uu___165_14566.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___165_14566.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___166_14593 = comp  in
            let uu____14594 =
              let uu____14595 =
                let uu____14604 = norm cfg env [] t  in
                let uu____14605 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____14604, uu____14605)  in
              FStar_Syntax_Syntax.GTotal uu____14595  in
            {
              FStar_Syntax_Syntax.n = uu____14594;
              FStar_Syntax_Syntax.pos =
                (uu___166_14593.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___166_14593.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____14657  ->
                      match uu____14657 with
                      | (a,i) ->
                          let uu____14668 = norm cfg env [] a  in
                          (uu____14668, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___88_14679  ->
                      match uu___88_14679 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____14683 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____14683
                      | f -> f))
               in
            let uu___167_14687 = comp  in
            let uu____14688 =
              let uu____14689 =
                let uu___168_14690 = ct  in
                let uu____14691 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____14692 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____14695 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____14691;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___168_14690.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____14692;
                  FStar_Syntax_Syntax.effect_args = uu____14695;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____14689  in
            {
              FStar_Syntax_Syntax.n = uu____14688;
              FStar_Syntax_Syntax.pos =
                (uu___167_14687.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___167_14687.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____14706  ->
        match uu____14706 with
        | (x,imp) ->
            let uu____14709 =
              let uu___169_14710 = x  in
              let uu____14711 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___169_14710.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___169_14710.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____14711
              }  in
            (uu____14709, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____14717 =
          FStar_List.fold_left
            (fun uu____14735  ->
               fun b  ->
                 match uu____14735 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____14717 with | (nbs,uu____14775) -> FStar_List.rev nbs

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
            let uu____14791 =
              let uu___170_14792 = rc  in
              let uu____14793 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___170_14792.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____14793;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___170_14792.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____14791
        | uu____14800 -> lopt

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
            (let uu____14821 = FStar_Syntax_Print.term_to_string tm  in
             let uu____14822 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____14821
               uu____14822)
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
          let uu____14842 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____14842
          then tm1
          else
            (let w t =
               let uu___171_14854 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___171_14854.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___171_14854.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____14863 =
                 let uu____14864 = FStar_Syntax_Util.unmeta t  in
                 uu____14864.FStar_Syntax_Syntax.n  in
               match uu____14863 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____14871 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____14916)::args1,(bv,uu____14919)::bs1) ->
                   let uu____14953 =
                     let uu____14954 = FStar_Syntax_Subst.compress t  in
                     uu____14954.FStar_Syntax_Syntax.n  in
                   (match uu____14953 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____14958 -> false)
               | ([],[]) -> true
               | (uu____14979,uu____14980) -> false  in
             let is_applied bs t =
               let uu____15016 = FStar_Syntax_Util.head_and_args' t  in
               match uu____15016 with
               | (hd1,args) ->
                   let uu____15049 =
                     let uu____15050 = FStar_Syntax_Subst.compress hd1  in
                     uu____15050.FStar_Syntax_Syntax.n  in
                   (match uu____15049 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____15056 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____15068 = FStar_Syntax_Util.is_squash t  in
               match uu____15068 with
               | FStar_Pervasives_Native.Some (uu____15079,t') ->
                   is_applied bs t'
               | uu____15091 ->
                   let uu____15100 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____15100 with
                    | FStar_Pervasives_Native.Some (uu____15111,t') ->
                        is_applied bs t'
                    | uu____15123 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____15140 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15140 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____15147)::(q,uu____15149)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____15184 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____15184 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____15189 =
                          let uu____15190 = FStar_Syntax_Subst.compress p  in
                          uu____15190.FStar_Syntax_Syntax.n  in
                        (match uu____15189 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15196 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____15196
                         | uu____15197 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____15200)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____15225 =
                          let uu____15226 = FStar_Syntax_Subst.compress p1
                             in
                          uu____15226.FStar_Syntax_Syntax.n  in
                        (match uu____15225 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15232 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____15232
                         | uu____15233 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____15237 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____15237 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____15242 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____15242 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____15249 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____15249
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____15252)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____15277 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____15277 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____15284 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____15284
                              | uu____15285 -> FStar_Pervasives_Native.None)
                         | uu____15288 -> FStar_Pervasives_Native.None)
                    | uu____15291 -> FStar_Pervasives_Native.None)
               | uu____15294 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____15305 =
                 let uu____15306 = FStar_Syntax_Subst.compress phi  in
                 uu____15306.FStar_Syntax_Syntax.n  in
               match uu____15305 with
               | FStar_Syntax_Syntax.Tm_match (uu____15311,br::brs) ->
                   let uu____15378 = br  in
                   (match uu____15378 with
                    | (uu____15395,uu____15396,e) ->
                        let r =
                          let uu____15417 = simp_t e  in
                          match uu____15417 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____15423 =
                                FStar_List.for_all
                                  (fun uu____15441  ->
                                     match uu____15441 with
                                     | (uu____15454,uu____15455,e') ->
                                         let uu____15469 = simp_t e'  in
                                         uu____15469 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____15423
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____15477 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____15482 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____15482
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____15503 =
                 match uu____15503 with
                 | (t1,q) ->
                     let uu____15516 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____15516 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____15544 -> (t1, q))
                  in
               let uu____15553 = FStar_Syntax_Util.head_and_args t  in
               match uu____15553 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____15615 =
                 let uu____15616 = FStar_Syntax_Util.unmeta ty  in
                 uu____15616.FStar_Syntax_Syntax.n  in
               match uu____15615 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____15620) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____15625,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____15645 -> false  in
             let simplify1 arg =
               let uu____15668 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____15668, arg)  in
             let uu____15677 = is_quantified_const tm1  in
             match uu____15677 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____15681 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____15681
             | FStar_Pervasives_Native.None  ->
                 let uu____15682 =
                   let uu____15683 = FStar_Syntax_Subst.compress tm1  in
                   uu____15683.FStar_Syntax_Syntax.n  in
                 (match uu____15682 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____15687;
                              FStar_Syntax_Syntax.vars = uu____15688;_},uu____15689);
                         FStar_Syntax_Syntax.pos = uu____15690;
                         FStar_Syntax_Syntax.vars = uu____15691;_},args)
                      ->
                      let uu____15717 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____15717
                      then
                        let uu____15718 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____15718 with
                         | (FStar_Pervasives_Native.Some (true ),uu____15765)::
                             (uu____15766,(arg,uu____15768))::[] ->
                             maybe_auto_squash arg
                         | (uu____15817,(arg,uu____15819))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____15820)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____15869)::uu____15870::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____15921::(FStar_Pervasives_Native.Some (false
                                         ),uu____15922)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____15973 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____15987 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____15987
                         then
                           let uu____15988 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____15988 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____16035)::uu____16036::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16087::(FStar_Pervasives_Native.Some (true
                                           ),uu____16088)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____16139)::(uu____16140,(arg,uu____16142))::[]
                               -> maybe_auto_squash arg
                           | (uu____16191,(arg,uu____16193))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____16194)::[]
                               -> maybe_auto_squash arg
                           | uu____16243 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____16257 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____16257
                            then
                              let uu____16258 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____16258 with
                              | uu____16305::(FStar_Pervasives_Native.Some
                                              (true ),uu____16306)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____16357)::uu____16358::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____16409)::(uu____16410,(arg,uu____16412))::[]
                                  -> maybe_auto_squash arg
                              | (uu____16461,(p,uu____16463))::(uu____16464,
                                                                (q,uu____16466))::[]
                                  ->
                                  let uu____16513 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____16513
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____16515 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____16529 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____16529
                               then
                                 let uu____16530 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____16530 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16577)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16578)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16629)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16630)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16681)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16682)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16733)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16734)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____16785,(arg,uu____16787))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____16788)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16837)::(uu____16838,(arg,uu____16840))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____16889,(arg,uu____16891))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____16892)::[]
                                     ->
                                     let uu____16941 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____16941
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16942)::(uu____16943,(arg,uu____16945))::[]
                                     ->
                                     let uu____16994 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____16994
                                 | (uu____16995,(p,uu____16997))::(uu____16998,
                                                                   (q,uu____17000))::[]
                                     ->
                                     let uu____17047 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____17047
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17049 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17063 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____17063
                                  then
                                    let uu____17064 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____17064 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____17111)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____17142)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17173 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17187 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____17187
                                     then
                                       match args with
                                       | (t,uu____17189)::[] ->
                                           let uu____17206 =
                                             let uu____17207 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17207.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17206 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17210::[],body,uu____17212)
                                                ->
                                                let uu____17239 = simp_t body
                                                   in
                                                (match uu____17239 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____17242 -> tm1)
                                            | uu____17245 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____17247))::(t,uu____17249)::[]
                                           ->
                                           let uu____17288 =
                                             let uu____17289 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17289.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17288 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17292::[],body,uu____17294)
                                                ->
                                                let uu____17321 = simp_t body
                                                   in
                                                (match uu____17321 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____17324 -> tm1)
                                            | uu____17327 -> tm1)
                                       | uu____17328 -> tm1
                                     else
                                       (let uu____17338 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____17338
                                        then
                                          match args with
                                          | (t,uu____17340)::[] ->
                                              let uu____17357 =
                                                let uu____17358 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17358.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17357 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17361::[],body,uu____17363)
                                                   ->
                                                   let uu____17390 =
                                                     simp_t body  in
                                                   (match uu____17390 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____17393 -> tm1)
                                               | uu____17396 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____17398))::(t,uu____17400)::[]
                                              ->
                                              let uu____17439 =
                                                let uu____17440 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17440.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17439 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17443::[],body,uu____17445)
                                                   ->
                                                   let uu____17472 =
                                                     simp_t body  in
                                                   (match uu____17472 with
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
                                                    | uu____17475 -> tm1)
                                               | uu____17478 -> tm1)
                                          | uu____17479 -> tm1
                                        else
                                          (let uu____17489 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____17489
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17490;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17491;_},uu____17492)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17509;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17510;_},uu____17511)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____17528 -> tm1
                                           else
                                             (let uu____17538 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____17538 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____17558 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____17568;
                         FStar_Syntax_Syntax.vars = uu____17569;_},args)
                      ->
                      let uu____17591 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____17591
                      then
                        let uu____17592 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____17592 with
                         | (FStar_Pervasives_Native.Some (true ),uu____17639)::
                             (uu____17640,(arg,uu____17642))::[] ->
                             maybe_auto_squash arg
                         | (uu____17691,(arg,uu____17693))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____17694)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____17743)::uu____17744::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____17795::(FStar_Pervasives_Native.Some (false
                                         ),uu____17796)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____17847 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____17861 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____17861
                         then
                           let uu____17862 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____17862 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____17909)::uu____17910::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____17961::(FStar_Pervasives_Native.Some (true
                                           ),uu____17962)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18013)::(uu____18014,(arg,uu____18016))::[]
                               -> maybe_auto_squash arg
                           | (uu____18065,(arg,uu____18067))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18068)::[]
                               -> maybe_auto_squash arg
                           | uu____18117 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18131 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18131
                            then
                              let uu____18132 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18132 with
                              | uu____18179::(FStar_Pervasives_Native.Some
                                              (true ),uu____18180)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18231)::uu____18232::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18283)::(uu____18284,(arg,uu____18286))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18335,(p,uu____18337))::(uu____18338,
                                                                (q,uu____18340))::[]
                                  ->
                                  let uu____18387 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____18387
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18389 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18403 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____18403
                               then
                                 let uu____18404 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____18404 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18451)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18452)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18503)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18504)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18555)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18556)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18607)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18608)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____18659,(arg,uu____18661))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____18662)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18711)::(uu____18712,(arg,uu____18714))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____18763,(arg,uu____18765))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____18766)::[]
                                     ->
                                     let uu____18815 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18815
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18816)::(uu____18817,(arg,uu____18819))::[]
                                     ->
                                     let uu____18868 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18868
                                 | (uu____18869,(p,uu____18871))::(uu____18872,
                                                                   (q,uu____18874))::[]
                                     ->
                                     let uu____18921 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____18921
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____18923 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____18937 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____18937
                                  then
                                    let uu____18938 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____18938 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____18985)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19016)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19047 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19061 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19061
                                     then
                                       match args with
                                       | (t,uu____19063)::[] ->
                                           let uu____19080 =
                                             let uu____19081 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19081.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19080 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19084::[],body,uu____19086)
                                                ->
                                                let uu____19113 = simp_t body
                                                   in
                                                (match uu____19113 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19116 -> tm1)
                                            | uu____19119 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19121))::(t,uu____19123)::[]
                                           ->
                                           let uu____19162 =
                                             let uu____19163 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19163.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19162 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19166::[],body,uu____19168)
                                                ->
                                                let uu____19195 = simp_t body
                                                   in
                                                (match uu____19195 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19198 -> tm1)
                                            | uu____19201 -> tm1)
                                       | uu____19202 -> tm1
                                     else
                                       (let uu____19212 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____19212
                                        then
                                          match args with
                                          | (t,uu____19214)::[] ->
                                              let uu____19231 =
                                                let uu____19232 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19232.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19231 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19235::[],body,uu____19237)
                                                   ->
                                                   let uu____19264 =
                                                     simp_t body  in
                                                   (match uu____19264 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____19267 -> tm1)
                                               | uu____19270 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____19272))::(t,uu____19274)::[]
                                              ->
                                              let uu____19313 =
                                                let uu____19314 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19314.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19313 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19317::[],body,uu____19319)
                                                   ->
                                                   let uu____19346 =
                                                     simp_t body  in
                                                   (match uu____19346 with
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
                                                    | uu____19349 -> tm1)
                                               | uu____19352 -> tm1)
                                          | uu____19353 -> tm1
                                        else
                                          (let uu____19363 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____19363
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19364;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19365;_},uu____19366)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19383;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19384;_},uu____19385)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____19402 -> tm1
                                           else
                                             (let uu____19412 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____19412 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____19432 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____19447 = simp_t t  in
                      (match uu____19447 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____19450 ->
                      let uu____19473 = is_const_match tm1  in
                      (match uu____19473 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____19476 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____19487  ->
               let uu____19488 = FStar_Syntax_Print.tag_of_term t  in
               let uu____19489 = FStar_Syntax_Print.term_to_string t  in
               let uu____19490 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____19497 =
                 let uu____19498 =
                   let uu____19501 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____19501
                    in
                 stack_to_string uu____19498  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____19488 uu____19489 uu____19490 uu____19497);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____19532 =
                     let uu____19533 =
                       let uu____19534 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____19534  in
                     FStar_Util.string_of_int uu____19533  in
                   let uu____19539 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____19540 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____19532 uu____19539 uu____19540)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____19594  ->
                     let uu____19595 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____19595);
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
               let uu____19631 =
                 let uu___172_19632 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___172_19632.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___172_19632.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____19631
           | (Arg (Univ uu____19633,uu____19634,uu____19635))::uu____19636 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____19639,uu____19640))::uu____19641 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____19656,uu____19657),aq,r))::stack1
               when
               let uu____19707 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____19707 ->
               let t2 =
                 let uu____19711 =
                   let uu____19712 =
                     let uu____19713 = closure_as_term cfg env_arg tm  in
                     (uu____19713, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____19712  in
                 uu____19711 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____19719),aq,r))::stack1 ->
               (log cfg
                  (fun uu____19772  ->
                     let uu____19773 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____19773);
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
                  (let uu____19783 = FStar_ST.op_Bang m  in
                   match uu____19783 with
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
                   | FStar_Pervasives_Native.Some (uu____19920,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____19967 =
                 log cfg
                   (fun uu____19971  ->
                      let uu____19972 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____19972);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____19976 =
                 let uu____19977 = FStar_Syntax_Subst.compress t1  in
                 uu____19977.FStar_Syntax_Syntax.n  in
               (match uu____19976 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____20004 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____20004  in
                    (log cfg
                       (fun uu____20008  ->
                          let uu____20009 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____20009);
                     (let uu____20010 = FStar_List.tl stack  in
                      norm cfg env1 uu____20010 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____20011);
                       FStar_Syntax_Syntax.pos = uu____20012;
                       FStar_Syntax_Syntax.vars = uu____20013;_},(e,uu____20015)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____20044 when
                    (cfg.steps).primops ->
                    let uu____20059 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____20059 with
                     | (hd1,args) ->
                         let uu____20096 =
                           let uu____20097 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____20097.FStar_Syntax_Syntax.n  in
                         (match uu____20096 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____20101 = find_prim_step cfg fv  in
                              (match uu____20101 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____20104; arity = uu____20105;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____20107;
                                     requires_binder_substitution =
                                       uu____20108;
                                     interpretation = uu____20109;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____20122 -> fallback " (3)" ())
                          | uu____20125 -> fallback " (4)" ()))
                | uu____20126 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____20146  ->
                     let uu____20147 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____20147);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____20152 =
                   log cfg
                     (fun uu____20157  ->
                        let uu____20158 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____20159 =
                          let uu____20160 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____20177  ->
                                    match uu____20177 with
                                    | (p,uu____20187,uu____20188) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____20160
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____20158 uu____20159);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___89_20205  ->
                                match uu___89_20205 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____20206 -> false))
                         in
                      let uu___173_20207 = cfg  in
                      {
                        steps =
                          (let uu___174_20210 = cfg.steps  in
                           {
                             beta = (uu___174_20210.beta);
                             iota = (uu___174_20210.iota);
                             zeta = false;
                             weak = (uu___174_20210.weak);
                             hnf = (uu___174_20210.hnf);
                             primops = (uu___174_20210.primops);
                             no_delta_steps = (uu___174_20210.no_delta_steps);
                             unfold_until = (uu___174_20210.unfold_until);
                             unfold_only = (uu___174_20210.unfold_only);
                             unfold_attr = (uu___174_20210.unfold_attr);
                             unfold_tac = (uu___174_20210.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___174_20210.pure_subterms_within_computations);
                             simplify = (uu___174_20210.simplify);
                             erase_universes =
                               (uu___174_20210.erase_universes);
                             allow_unbound_universes =
                               (uu___174_20210.allow_unbound_universes);
                             reify_ = (uu___174_20210.reify_);
                             compress_uvars = (uu___174_20210.compress_uvars);
                             no_full_norm = (uu___174_20210.no_full_norm);
                             check_no_uvars = (uu___174_20210.check_no_uvars);
                             unmeta = (uu___174_20210.unmeta);
                             unascribe = (uu___174_20210.unascribe)
                           });
                        tcenv = (uu___173_20207.tcenv);
                        debug = (uu___173_20207.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___173_20207.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___173_20207.memoize_lazy);
                        normalize_pure_lets =
                          (uu___173_20207.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____20242 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____20263 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____20323  ->
                                    fun uu____20324  ->
                                      match (uu____20323, uu____20324) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____20415 = norm_pat env3 p1
                                             in
                                          (match uu____20415 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____20263 with
                           | (pats1,env3) ->
                               ((let uu___175_20497 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___175_20497.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___176_20516 = x  in
                            let uu____20517 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___176_20516.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___176_20516.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20517
                            }  in
                          ((let uu___177_20531 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___177_20531.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___178_20542 = x  in
                            let uu____20543 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___178_20542.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___178_20542.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20543
                            }  in
                          ((let uu___179_20557 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___179_20557.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___180_20573 = x  in
                            let uu____20574 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___180_20573.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___180_20573.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20574
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___181_20581 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___181_20581.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____20591 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____20605 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____20605 with
                                  | (p,wopt,e) ->
                                      let uu____20625 = norm_pat env1 p  in
                                      (match uu____20625 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____20650 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____20650
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____20656 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____20656)
                    in
                 let rec is_cons head1 =
                   let uu____20661 =
                     let uu____20662 = FStar_Syntax_Subst.compress head1  in
                     uu____20662.FStar_Syntax_Syntax.n  in
                   match uu____20661 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____20666) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____20671 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20672;
                         FStar_Syntax_Syntax.fv_delta = uu____20673;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20674;
                         FStar_Syntax_Syntax.fv_delta = uu____20675;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____20676);_}
                       -> true
                   | uu____20683 -> false  in
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
                   let uu____20828 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____20828 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____20915 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____20954 ->
                                 let uu____20955 =
                                   let uu____20956 = is_cons head1  in
                                   Prims.op_Negation uu____20956  in
                                 FStar_Util.Inr uu____20955)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____20981 =
                              let uu____20982 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____20982.FStar_Syntax_Syntax.n  in
                            (match uu____20981 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____21000 ->
                                 let uu____21001 =
                                   let uu____21002 = is_cons head1  in
                                   Prims.op_Negation uu____21002  in
                                 FStar_Util.Inr uu____21001))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____21071)::rest_a,(p1,uu____21074)::rest_p) ->
                       let uu____21118 = matches_pat t2 p1  in
                       (match uu____21118 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____21167 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____21273 = matches_pat scrutinee1 p1  in
                       (match uu____21273 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____21313  ->
                                  let uu____21314 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____21315 =
                                    let uu____21316 =
                                      FStar_List.map
                                        (fun uu____21326  ->
                                           match uu____21326 with
                                           | (uu____21331,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____21316
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____21314 uu____21315);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____21362  ->
                                       match uu____21362 with
                                       | (bv,t2) ->
                                           let uu____21385 =
                                             let uu____21392 =
                                               let uu____21395 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____21395
                                                in
                                             let uu____21396 =
                                               let uu____21397 =
                                                 let uu____21428 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____21428, false)
                                                  in
                                               Clos uu____21397  in
                                             (uu____21392, uu____21396)  in
                                           uu____21385 :: env2) env1 s
                                 in
                              let uu____21545 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____21545)))
                    in
                 if (cfg.steps).iota
                 then matches scrutinee branches
                 else norm_and_rebuild_match ())))

let (plugins :
  (primitive_step -> Prims.unit,Prims.unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____21568 =
      let uu____21571 = FStar_ST.op_Bang plugins  in p :: uu____21571  in
    FStar_ST.op_Colon_Equals plugins uu____21568  in
  let retrieve uu____21669 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____21734  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___90_21767  ->
                  match uu___90_21767 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____21771 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____21777 -> d  in
        let uu____21780 = to_fsteps s  in
        let uu____21781 =
          let uu____21782 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____21783 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____21784 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____21785 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____21786 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____21782;
            primop = uu____21783;
            b380 = uu____21784;
            norm_delayed = uu____21785;
            print_normalized = uu____21786
          }  in
        let uu____21787 =
          let uu____21790 =
            let uu____21793 = retrieve_plugins ()  in
            FStar_List.append uu____21793 psteps  in
          add_steps built_in_primitive_steps uu____21790  in
        let uu____21796 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____21798 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____21798)
           in
        {
          steps = uu____21780;
          tcenv = e;
          debug = uu____21781;
          delta_level = d1;
          primitive_steps = uu____21787;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____21796
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
      fun t  -> let uu____21856 = config s e  in norm_comp uu____21856 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____21869 = config [] env  in norm_universe uu____21869 [] u
  
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
        let uu____21887 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21887  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____21894 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___182_21913 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___182_21913.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___182_21913.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____21920 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____21920
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
                  let uu___183_21929 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___183_21929.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___183_21929.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___183_21929.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___184_21931 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___184_21931.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___184_21931.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___184_21931.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___184_21931.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___185_21932 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___185_21932.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___185_21932.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____21934 -> c
  
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
        let uu____21946 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21946  in
      let uu____21953 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____21953
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____21957  ->
                 let uu____21958 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____21958)
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
            ((let uu____21975 =
                let uu____21980 =
                  let uu____21981 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____21981
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____21980)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____21975);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____21992 = config [AllowUnboundUniverses] env  in
          norm_comp uu____21992 [] c
        with
        | e ->
            ((let uu____22005 =
                let uu____22010 =
                  let uu____22011 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22011
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22010)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____22005);
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
                   let uu____22048 =
                     let uu____22049 =
                       let uu____22056 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____22056)  in
                     FStar_Syntax_Syntax.Tm_refine uu____22049  in
                   mk uu____22048 t01.FStar_Syntax_Syntax.pos
               | uu____22061 -> t2)
          | uu____22062 -> t2  in
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
        let uu____22102 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____22102 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____22131 ->
                 let uu____22138 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____22138 with
                  | (actuals,uu____22148,uu____22149) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____22163 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____22163 with
                         | (binders,args) ->
                             let uu____22180 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____22180
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
      | uu____22188 ->
          let uu____22189 = FStar_Syntax_Util.head_and_args t  in
          (match uu____22189 with
           | (head1,args) ->
               let uu____22226 =
                 let uu____22227 = FStar_Syntax_Subst.compress head1  in
                 uu____22227.FStar_Syntax_Syntax.n  in
               (match uu____22226 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____22230,thead) ->
                    let uu____22256 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____22256 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____22298 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___190_22306 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___190_22306.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___190_22306.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___190_22306.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___190_22306.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___190_22306.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___190_22306.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___190_22306.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___190_22306.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___190_22306.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___190_22306.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___190_22306.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___190_22306.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___190_22306.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___190_22306.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___190_22306.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___190_22306.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___190_22306.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___190_22306.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___190_22306.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___190_22306.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___190_22306.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___190_22306.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___190_22306.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___190_22306.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___190_22306.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___190_22306.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___190_22306.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___190_22306.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___190_22306.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___190_22306.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___190_22306.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___190_22306.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___190_22306.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____22298 with
                            | (uu____22307,ty,uu____22309) ->
                                eta_expand_with_type env t ty))
                | uu____22310 ->
                    let uu____22311 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___191_22319 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___191_22319.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___191_22319.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___191_22319.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___191_22319.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___191_22319.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___191_22319.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___191_22319.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___191_22319.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___191_22319.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___191_22319.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___191_22319.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___191_22319.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___191_22319.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___191_22319.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___191_22319.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___191_22319.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___191_22319.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___191_22319.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___191_22319.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___191_22319.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___191_22319.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___191_22319.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___191_22319.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___191_22319.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___191_22319.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___191_22319.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___191_22319.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___191_22319.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___191_22319.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___191_22319.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___191_22319.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___191_22319.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___191_22319.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____22311 with
                     | (uu____22320,ty,uu____22322) ->
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
      let uu___192_22379 = x  in
      let uu____22380 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___192_22379.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___192_22379.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____22380
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____22383 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____22408 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____22409 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____22410 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____22411 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____22418 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____22419 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____22420 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___193_22448 = rc  in
          let uu____22449 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____22456 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___193_22448.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____22449;
            FStar_Syntax_Syntax.residual_flags = uu____22456
          }  in
        let uu____22459 =
          let uu____22460 =
            let uu____22477 = elim_delayed_subst_binders bs  in
            let uu____22484 = elim_delayed_subst_term t2  in
            let uu____22485 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____22477, uu____22484, uu____22485)  in
          FStar_Syntax_Syntax.Tm_abs uu____22460  in
        mk1 uu____22459
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____22514 =
          let uu____22515 =
            let uu____22528 = elim_delayed_subst_binders bs  in
            let uu____22535 = elim_delayed_subst_comp c  in
            (uu____22528, uu____22535)  in
          FStar_Syntax_Syntax.Tm_arrow uu____22515  in
        mk1 uu____22514
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____22548 =
          let uu____22549 =
            let uu____22556 = elim_bv bv  in
            let uu____22557 = elim_delayed_subst_term phi  in
            (uu____22556, uu____22557)  in
          FStar_Syntax_Syntax.Tm_refine uu____22549  in
        mk1 uu____22548
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____22580 =
          let uu____22581 =
            let uu____22596 = elim_delayed_subst_term t2  in
            let uu____22597 = elim_delayed_subst_args args  in
            (uu____22596, uu____22597)  in
          FStar_Syntax_Syntax.Tm_app uu____22581  in
        mk1 uu____22580
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___194_22661 = p  in
              let uu____22662 =
                let uu____22663 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____22663  in
              {
                FStar_Syntax_Syntax.v = uu____22662;
                FStar_Syntax_Syntax.p =
                  (uu___194_22661.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___195_22665 = p  in
              let uu____22666 =
                let uu____22667 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____22667  in
              {
                FStar_Syntax_Syntax.v = uu____22666;
                FStar_Syntax_Syntax.p =
                  (uu___195_22665.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___196_22674 = p  in
              let uu____22675 =
                let uu____22676 =
                  let uu____22683 = elim_bv x  in
                  let uu____22684 = elim_delayed_subst_term t0  in
                  (uu____22683, uu____22684)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____22676  in
              {
                FStar_Syntax_Syntax.v = uu____22675;
                FStar_Syntax_Syntax.p =
                  (uu___196_22674.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___197_22703 = p  in
              let uu____22704 =
                let uu____22705 =
                  let uu____22718 =
                    FStar_List.map
                      (fun uu____22741  ->
                         match uu____22741 with
                         | (x,b) ->
                             let uu____22754 = elim_pat x  in
                             (uu____22754, b)) pats
                     in
                  (fv, uu____22718)  in
                FStar_Syntax_Syntax.Pat_cons uu____22705  in
              {
                FStar_Syntax_Syntax.v = uu____22704;
                FStar_Syntax_Syntax.p =
                  (uu___197_22703.FStar_Syntax_Syntax.p)
              }
          | uu____22767 -> p  in
        let elim_branch uu____22789 =
          match uu____22789 with
          | (pat,wopt,t3) ->
              let uu____22815 = elim_pat pat  in
              let uu____22818 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____22821 = elim_delayed_subst_term t3  in
              (uu____22815, uu____22818, uu____22821)
           in
        let uu____22826 =
          let uu____22827 =
            let uu____22850 = elim_delayed_subst_term t2  in
            let uu____22851 = FStar_List.map elim_branch branches  in
            (uu____22850, uu____22851)  in
          FStar_Syntax_Syntax.Tm_match uu____22827  in
        mk1 uu____22826
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____22960 =
          match uu____22960 with
          | (tc,topt) ->
              let uu____22995 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____23005 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____23005
                | FStar_Util.Inr c ->
                    let uu____23007 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____23007
                 in
              let uu____23008 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____22995, uu____23008)
           in
        let uu____23017 =
          let uu____23018 =
            let uu____23045 = elim_delayed_subst_term t2  in
            let uu____23046 = elim_ascription a  in
            (uu____23045, uu____23046, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____23018  in
        mk1 uu____23017
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___198_23091 = lb  in
          let uu____23092 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____23095 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___198_23091.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___198_23091.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____23092;
            FStar_Syntax_Syntax.lbeff =
              (uu___198_23091.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____23095;
            FStar_Syntax_Syntax.lbattrs =
              (uu___198_23091.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___198_23091.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____23098 =
          let uu____23099 =
            let uu____23112 =
              let uu____23119 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____23119)  in
            let uu____23128 = elim_delayed_subst_term t2  in
            (uu____23112, uu____23128)  in
          FStar_Syntax_Syntax.Tm_let uu____23099  in
        mk1 uu____23098
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____23161 =
          let uu____23162 =
            let uu____23179 = elim_delayed_subst_term t2  in
            (uv, uu____23179)  in
          FStar_Syntax_Syntax.Tm_uvar uu____23162  in
        mk1 uu____23161
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____23197 =
          let uu____23198 =
            let uu____23205 = elim_delayed_subst_term tm  in
            (uu____23205, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____23198  in
        mk1 uu____23197
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____23212 =
          let uu____23213 =
            let uu____23220 = elim_delayed_subst_term t2  in
            let uu____23221 = elim_delayed_subst_meta md  in
            (uu____23220, uu____23221)  in
          FStar_Syntax_Syntax.Tm_meta uu____23213  in
        mk1 uu____23212

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___91_23228  ->
         match uu___91_23228 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____23232 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____23232
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
        let uu____23253 =
          let uu____23254 =
            let uu____23263 = elim_delayed_subst_term t  in
            (uu____23263, uopt)  in
          FStar_Syntax_Syntax.Total uu____23254  in
        mk1 uu____23253
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____23276 =
          let uu____23277 =
            let uu____23286 = elim_delayed_subst_term t  in
            (uu____23286, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____23277  in
        mk1 uu____23276
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___199_23291 = ct  in
          let uu____23292 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____23295 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____23304 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___199_23291.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___199_23291.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____23292;
            FStar_Syntax_Syntax.effect_args = uu____23295;
            FStar_Syntax_Syntax.flags = uu____23304
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___92_23307  ->
    match uu___92_23307 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____23319 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____23319
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____23352 =
          let uu____23359 = elim_delayed_subst_term t  in (m, uu____23359)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____23352
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____23367 =
          let uu____23376 = elim_delayed_subst_term t  in
          (m1, m2, uu____23376)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____23367
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____23399  ->
         match uu____23399 with
         | (t,q) ->
             let uu____23410 = elim_delayed_subst_term t  in (uu____23410, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____23430  ->
         match uu____23430 with
         | (x,q) ->
             let uu____23441 =
               let uu___200_23442 = x  in
               let uu____23443 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___200_23442.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___200_23442.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____23443
               }  in
             (uu____23441, q)) bs

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
            | (uu____23519,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____23525,FStar_Util.Inl t) ->
                let uu____23531 =
                  let uu____23534 =
                    let uu____23535 =
                      let uu____23548 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____23548)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____23535  in
                  FStar_Syntax_Syntax.mk uu____23534  in
                uu____23531 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____23552 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____23552 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____23580 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____23635 ->
                    let uu____23636 =
                      let uu____23645 =
                        let uu____23646 = FStar_Syntax_Subst.compress t4  in
                        uu____23646.FStar_Syntax_Syntax.n  in
                      (uu____23645, tc)  in
                    (match uu____23636 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____23671) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____23708) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____23747,FStar_Util.Inl uu____23748) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____23771 -> failwith "Impossible")
                 in
              (match uu____23580 with
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
          let uu____23876 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____23876 with
          | (univ_names1,binders1,tc) ->
              let uu____23934 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____23934)
  
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
          let uu____23969 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____23969 with
          | (univ_names1,binders1,tc) ->
              let uu____24029 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____24029)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____24062 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____24062 with
           | (univ_names1,binders1,typ1) ->
               let uu___201_24090 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___201_24090.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___201_24090.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___201_24090.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___201_24090.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___202_24111 = s  in
          let uu____24112 =
            let uu____24113 =
              let uu____24122 = FStar_List.map (elim_uvars env) sigs  in
              (uu____24122, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____24113  in
          {
            FStar_Syntax_Syntax.sigel = uu____24112;
            FStar_Syntax_Syntax.sigrng =
              (uu___202_24111.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___202_24111.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___202_24111.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___202_24111.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____24139 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24139 with
           | (univ_names1,uu____24157,typ1) ->
               let uu___203_24171 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___203_24171.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___203_24171.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___203_24171.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___203_24171.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____24177 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24177 with
           | (univ_names1,uu____24195,typ1) ->
               let uu___204_24209 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___204_24209.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___204_24209.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___204_24209.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___204_24209.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____24243 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____24243 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____24266 =
                            let uu____24267 =
                              let uu____24268 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____24268  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____24267
                             in
                          elim_delayed_subst_term uu____24266  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___205_24271 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___205_24271.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___205_24271.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___205_24271.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___205_24271.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___206_24272 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___206_24272.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___206_24272.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___206_24272.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___206_24272.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___207_24284 = s  in
          let uu____24285 =
            let uu____24286 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____24286  in
          {
            FStar_Syntax_Syntax.sigel = uu____24285;
            FStar_Syntax_Syntax.sigrng =
              (uu___207_24284.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___207_24284.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___207_24284.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___207_24284.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____24290 = elim_uvars_aux_t env us [] t  in
          (match uu____24290 with
           | (us1,uu____24308,t1) ->
               let uu___208_24322 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___208_24322.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___208_24322.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___208_24322.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___208_24322.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24323 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____24325 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____24325 with
           | (univs1,binders,signature) ->
               let uu____24353 =
                 let uu____24362 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____24362 with
                 | (univs_opening,univs2) ->
                     let uu____24389 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____24389)
                  in
               (match uu____24353 with
                | (univs_opening,univs_closing) ->
                    let uu____24406 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____24412 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____24413 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____24412, uu____24413)  in
                    (match uu____24406 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____24435 =
                           match uu____24435 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____24453 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____24453 with
                                | (us1,t1) ->
                                    let uu____24464 =
                                      let uu____24469 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____24476 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____24469, uu____24476)  in
                                    (match uu____24464 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____24489 =
                                           let uu____24494 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____24503 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____24494, uu____24503)  in
                                         (match uu____24489 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____24519 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____24519
                                                 in
                                              let uu____24520 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____24520 with
                                               | (uu____24541,uu____24542,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____24557 =
                                                       let uu____24558 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____24558
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____24557
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____24563 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____24563 with
                           | (uu____24576,uu____24577,t1) -> t1  in
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
                             | uu____24637 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____24654 =
                               let uu____24655 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____24655.FStar_Syntax_Syntax.n  in
                             match uu____24654 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____24714 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____24743 =
                               let uu____24744 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____24744.FStar_Syntax_Syntax.n  in
                             match uu____24743 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____24765) ->
                                 let uu____24786 = destruct_action_body body
                                    in
                                 (match uu____24786 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____24831 ->
                                 let uu____24832 = destruct_action_body t  in
                                 (match uu____24832 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____24881 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____24881 with
                           | (action_univs,t) ->
                               let uu____24890 = destruct_action_typ_templ t
                                  in
                               (match uu____24890 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___209_24931 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___209_24931.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___209_24931.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___210_24933 = ed  in
                           let uu____24934 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____24935 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____24936 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____24937 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____24938 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____24939 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____24940 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____24941 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____24942 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____24943 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____24944 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____24945 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____24946 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____24947 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___210_24933.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___210_24933.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____24934;
                             FStar_Syntax_Syntax.bind_wp = uu____24935;
                             FStar_Syntax_Syntax.if_then_else = uu____24936;
                             FStar_Syntax_Syntax.ite_wp = uu____24937;
                             FStar_Syntax_Syntax.stronger = uu____24938;
                             FStar_Syntax_Syntax.close_wp = uu____24939;
                             FStar_Syntax_Syntax.assert_p = uu____24940;
                             FStar_Syntax_Syntax.assume_p = uu____24941;
                             FStar_Syntax_Syntax.null_wp = uu____24942;
                             FStar_Syntax_Syntax.trivial = uu____24943;
                             FStar_Syntax_Syntax.repr = uu____24944;
                             FStar_Syntax_Syntax.return_repr = uu____24945;
                             FStar_Syntax_Syntax.bind_repr = uu____24946;
                             FStar_Syntax_Syntax.actions = uu____24947;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___210_24933.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___211_24950 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___211_24950.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___211_24950.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___211_24950.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___211_24950.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___93_24967 =
            match uu___93_24967 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____24994 = elim_uvars_aux_t env us [] t  in
                (match uu____24994 with
                 | (us1,uu____25018,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___212_25037 = sub_eff  in
            let uu____25038 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____25041 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___212_25037.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___212_25037.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____25038;
              FStar_Syntax_Syntax.lift = uu____25041
            }  in
          let uu___213_25044 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___213_25044.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___213_25044.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___213_25044.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___213_25044.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____25054 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____25054 with
           | (univ_names1,binders1,comp1) ->
               let uu___214_25088 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___214_25088.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___214_25088.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___214_25088.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___214_25088.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____25099 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____25100 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  