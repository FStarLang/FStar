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
  
let mk :
  'Auu____2338 .
    'Auu____2338 ->
      FStar_Range.range -> 'Auu____2338 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2392 = FStar_ST.op_Bang r  in
          match uu____2392 with
          | FStar_Pervasives_Native.Some uu____2440 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2494 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2494 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___78_2501  ->
    match uu___78_2501 with
    | Arg (c,uu____2503,uu____2504) ->
        let uu____2505 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2505
    | MemoLazy uu____2506 -> "MemoLazy"
    | Abs (uu____2513,bs,uu____2515,uu____2516,uu____2517) ->
        let uu____2522 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2522
    | UnivArgs uu____2527 -> "UnivArgs"
    | Match uu____2534 -> "Match"
    | App (uu____2541,t,uu____2543,uu____2544) ->
        let uu____2545 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2545
    | Meta (m,uu____2547) -> "Meta"
    | Let uu____2548 -> "Let"
    | Cfg uu____2557 -> "Cfg"
    | Debug (t,uu____2559) ->
        let uu____2560 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2560
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2568 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2568 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2599 . 'Auu____2599 Prims.list -> Prims.bool =
  fun uu___79_2605  ->
    match uu___79_2605 with | [] -> true | uu____2608 -> false
  
let lookup_bvar :
  'Auu____2615 'Auu____2616 .
    ('Auu____2615,'Auu____2616) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2616
  =
  fun env  ->
    fun x  ->
      try
        let uu____2640 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____2640
      with
      | uu____2653 ->
          let uu____2654 =
            let uu____2655 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____2655  in
          failwith uu____2654
  
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
          let uu____2692 =
            FStar_List.fold_left
              (fun uu____2718  ->
                 fun u1  ->
                   match uu____2718 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2743 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2743 with
                        | (k_u,n1) ->
                            let uu____2758 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____2758
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2692 with
          | (uu____2776,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2801 =
                   let uu____2802 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____2802  in
                 match uu____2801 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2820 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2828 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2834 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2843 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2852 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2859 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2859 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2876 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2876 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2884 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2892 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____2892 with
                                  | (uu____2897,m) -> n1 <= m))
                           in
                        if uu____2884 then rest1 else us1
                    | uu____2902 -> us1)
               | uu____2907 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2911 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____2911
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2915 = aux u  in
           match uu____2915 with
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
          (fun uu____3019  ->
             let uu____3020 = FStar_Syntax_Print.tag_of_term t  in
             let uu____3021 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3020
               uu____3021);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3028 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3030 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3055 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3056 -> t1
              | FStar_Syntax_Syntax.Tm_lazy uu____3057 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3058 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3059 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3076 =
                      let uu____3077 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____3078 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3077 uu____3078
                       in
                    failwith uu____3076
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3081 =
                    let uu____3082 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____3082  in
                  mk uu____3081 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3089 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3089
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3091 = lookup_bvar env x  in
                  (match uu____3091 with
                   | Univ uu____3094 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3097,uu____3098) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3210 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3210 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____3238 =
                         let uu____3239 =
                           let uu____3256 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____3256)  in
                         FStar_Syntax_Syntax.Tm_abs uu____3239  in
                       mk uu____3238 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3287 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3287 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3329 =
                    let uu____3340 =
                      let uu____3347 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3347]  in
                    closures_as_binders_delayed cfg env uu____3340  in
                  (match uu____3329 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____3365 =
                         let uu____3366 =
                           let uu____3373 =
                             let uu____3374 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____3374
                               FStar_Pervasives_Native.fst
                              in
                           (uu____3373, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____3366  in
                       mk uu____3365 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3465 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____3465
                    | FStar_Util.Inr c ->
                        let uu____3479 = close_comp cfg env c  in
                        FStar_Util.Inr uu____3479
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____3495 =
                    let uu____3496 =
                      let uu____3523 = closure_as_term_delayed cfg env t11
                         in
                      (uu____3523, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3496  in
                  mk uu____3495 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3574 =
                    let uu____3575 =
                      let uu____3582 = closure_as_term_delayed cfg env t'  in
                      let uu____3585 =
                        let uu____3586 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____3586  in
                      (uu____3582, uu____3585)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3575  in
                  mk uu____3574 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3646 =
                    let uu____3647 =
                      let uu____3654 = closure_as_term_delayed cfg env t'  in
                      let uu____3657 =
                        let uu____3658 =
                          let uu____3665 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____3665)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____3658  in
                      (uu____3654, uu____3657)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3647  in
                  mk uu____3646 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3684 =
                    let uu____3685 =
                      let uu____3692 = closure_as_term_delayed cfg env t'  in
                      let uu____3695 =
                        let uu____3696 =
                          let uu____3705 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____3705)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3696  in
                      (uu____3692, uu____3695)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3685  in
                  mk uu____3684 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_quoted (t'',qi)) ->
                  if qi.FStar_Syntax_Syntax.qopen
                  then
                    let uu____3723 =
                      let uu____3724 =
                        let uu____3731 = closure_as_term_delayed cfg env t'
                           in
                        let uu____3734 =
                          let uu____3735 =
                            let uu____3742 =
                              closure_as_term_delayed cfg env t''  in
                            (uu____3742, qi)  in
                          FStar_Syntax_Syntax.Meta_quoted uu____3735  in
                        (uu____3731, uu____3734)  in
                      FStar_Syntax_Syntax.Tm_meta uu____3724  in
                    mk uu____3723 t1.FStar_Syntax_Syntax.pos
                  else
                    (let uu____3750 =
                       let uu____3751 =
                         let uu____3758 = closure_as_term_delayed cfg env t'
                            in
                         (uu____3758,
                           (FStar_Syntax_Syntax.Meta_quoted (t'', qi)))
                          in
                       FStar_Syntax_Syntax.Tm_meta uu____3751  in
                     mk uu____3750 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3771 =
                    let uu____3772 =
                      let uu____3779 = closure_as_term_delayed cfg env t'  in
                      (uu____3779, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3772  in
                  mk uu____3771 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____3819  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____3838 =
                    let uu____3849 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____3849
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____3868 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___122_3880 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___122_3880.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___122_3880.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____3868))
                     in
                  (match uu____3838 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___123_3896 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___123_3896.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___123_3896.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___123_3896.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___123_3896.FStar_Syntax_Syntax.lbpos)
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____3907,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____3966  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____3991 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____3991
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____4011  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____4033 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4033
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___124_4045 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___124_4045.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___124_4045.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___125_4046 = lb  in
                    let uu____4047 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___125_4046.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___125_4046.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____4047;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___125_4046.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___125_4046.FStar_Syntax_Syntax.lbpos)
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4077  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____4166 =
                    match uu____4166 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4221 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4242 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4302  ->
                                        fun uu____4303  ->
                                          match (uu____4302, uu____4303) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4394 =
                                                norm_pat env3 p1  in
                                              (match uu____4394 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____4242 with
                               | (pats1,env3) ->
                                   ((let uu___126_4476 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___126_4476.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___127_4495 = x  in
                                let uu____4496 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___127_4495.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___127_4495.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4496
                                }  in
                              ((let uu___128_4510 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___128_4510.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___129_4521 = x  in
                                let uu____4522 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___129_4521.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___129_4521.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4522
                                }  in
                              ((let uu___130_4536 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___130_4536.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___131_4552 = x  in
                                let uu____4553 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___131_4552.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___131_4552.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4553
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___132_4560 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___132_4560.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____4563 = norm_pat env1 pat  in
                        (match uu____4563 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4592 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____4592
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____4598 =
                    let uu____4599 =
                      let uu____4622 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____4622)  in
                    FStar_Syntax_Syntax.Tm_match uu____4599  in
                  mk uu____4598 t1.FStar_Syntax_Syntax.pos))

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
        | uu____4708 -> closure_as_term cfg env t

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
        | uu____4734 ->
            FStar_List.map
              (fun uu____4751  ->
                 match uu____4751 with
                 | (x,imp) ->
                     let uu____4770 = closure_as_term_delayed cfg env x  in
                     (uu____4770, imp)) args

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
        let uu____4784 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4833  ->
                  fun uu____4834  ->
                    match (uu____4833, uu____4834) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___133_4904 = b  in
                          let uu____4905 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___133_4904.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___133_4904.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4905
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____4784 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____4998 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5011 = closure_as_term_delayed cfg env t  in
                 let uu____5012 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5011 uu____5012
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5025 = closure_as_term_delayed cfg env t  in
                 let uu____5026 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5025 uu____5026
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
                        (fun uu___80_5052  ->
                           match uu___80_5052 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5056 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____5056
                           | f -> f))
                    in
                 let uu____5060 =
                   let uu___134_5061 = c1  in
                   let uu____5062 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5062;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___134_5061.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5060)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___81_5072  ->
            match uu___81_5072 with
            | FStar_Syntax_Syntax.DECREASES uu____5073 -> false
            | uu____5076 -> true))

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
                   (fun uu___82_5094  ->
                      match uu___82_5094 with
                      | FStar_Syntax_Syntax.DECREASES uu____5095 -> false
                      | uu____5098 -> true))
               in
            let rc1 =
              let uu___135_5100 = rc  in
              let uu____5101 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___135_5100.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5101;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5108 -> lopt

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
    let uu____5193 = FStar_Syntax_Embeddings.unembed_list_safe u  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5193  in
  let arg_as_bounded_int uu____5221 =
    match uu____5221 with
    | (a,uu____5233) ->
        let uu____5240 =
          let uu____5241 = FStar_Syntax_Subst.compress a  in
          uu____5241.FStar_Syntax_Syntax.n  in
        (match uu____5240 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5251;
                FStar_Syntax_Syntax.vars = uu____5252;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5254;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5255;_},uu____5256)::[])
             when
             FStar_Util.ends_with
               (FStar_Ident.text_of_lid
                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
               "int_to_t"
             ->
             let uu____5295 =
               let uu____5300 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5300)  in
             FStar_Pervasives_Native.Some uu____5295
         | uu____5305 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5345 = f a  in FStar_Pervasives_Native.Some uu____5345
    | uu____5346 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5394 = f a0 a1  in FStar_Pervasives_Native.Some uu____5394
    | uu____5395 -> FStar_Pervasives_Native.None  in
  let unary_op a416 a417 a418 a419 a420 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5437 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a415  -> (Obj.magic (f res.psc_range)) a415)
                    uu____5437)) a416 a417 a418 a419 a420
     in
  let binary_op a423 a424 a425 a426 a427 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5486 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a421  ->
                       fun a422  -> (Obj.magic (f res.psc_range)) a421 a422)
                    uu____5486)) a423 a424 a425 a426 a427
     in
  let as_primitive_step uu____5510 =
    match uu____5510 with
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
                   let uu____5558 = f x  in
                   FStar_Syntax_Embeddings.embed_int r uu____5558)) a429 a430)
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
                       let uu____5586 = f x y  in
                       FStar_Syntax_Embeddings.embed_int r uu____5586)) a432
               a433 a434)
     in
  let unary_bool_op f =
    unary_op () (fun a435  -> (Obj.magic arg_as_bool) a435)
      (fun a436  ->
         fun a437  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5607 = f x  in
                   FStar_Syntax_Embeddings.embed_bool r uu____5607)) a436
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
                       let uu____5635 = f x y  in
                       FStar_Syntax_Embeddings.embed_bool r uu____5635)) a439
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
                       let uu____5663 = f x y  in
                       FStar_Syntax_Embeddings.embed_string r uu____5663))
               a443 a444 a445)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____5771 =
          let uu____5780 = as_a a  in
          let uu____5783 = as_b b  in (uu____5780, uu____5783)  in
        (match uu____5771 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____5798 =
               let uu____5799 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____5799  in
             FStar_Pervasives_Native.Some uu____5798
         | uu____5800 -> FStar_Pervasives_Native.None)
    | uu____5809 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____5823 =
        let uu____5824 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____5824  in
      mk uu____5823 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____5834 =
      let uu____5837 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____5837  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____5834  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____5869 =
      let uu____5870 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____5870  in
    FStar_Syntax_Embeddings.embed_int rng uu____5869  in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____5888 = arg_as_string a1  in
        (match uu____5888 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5894 =
               Obj.magic
                 (arg_as_list ()
                    (Obj.magic FStar_Syntax_Embeddings.unembed_string_safe)
                    a2)
                in
             (match uu____5894 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5907 =
                    FStar_Syntax_Embeddings.embed_string psc.psc_range r  in
                  FStar_Pervasives_Native.Some uu____5907
              | uu____5908 -> FStar_Pervasives_Native.None)
         | uu____5913 -> FStar_Pervasives_Native.None)
    | uu____5916 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____5926 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed_string rng uu____5926  in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed_string rng (if b then "true" else "false")
     in
  let term_of_range r =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range r))
      FStar_Pervasives_Native.None r
     in
  let mk_range1 uu____5950 args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____5961 =
          let uu____5982 = arg_as_string fn  in
          let uu____5985 = arg_as_int from_line  in
          let uu____5988 = arg_as_int from_col  in
          let uu____5991 = arg_as_int to_line  in
          let uu____5994 = arg_as_int to_col  in
          (uu____5982, uu____5985, uu____5988, uu____5991, uu____5994)  in
        (match uu____5961 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6025 =
                 let uu____6026 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6027 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6026 uu____6027  in
               let uu____6028 =
                 let uu____6029 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6030 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6029 uu____6030  in
               FStar_Range.mk_range fn1 uu____6025 uu____6028  in
             let uu____6031 = term_of_range r  in
             FStar_Pervasives_Native.Some uu____6031
         | uu____6036 -> FStar_Pervasives_Native.None)
    | uu____6057 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6084)::(a1,uu____6086)::(a2,uu____6088)::[] ->
        let uu____6125 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6125 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6138 -> FStar_Pervasives_Native.None)
    | uu____6139 -> failwith "Unexpected number of arguments"  in
  let idstep psc args =
    match args with
    | (a1,uu____6166)::[] -> FStar_Pervasives_Native.Some a1
    | uu____6175 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6199 =
      let uu____6214 =
        let uu____6229 =
          let uu____6244 =
            let uu____6259 =
              let uu____6274 =
                let uu____6289 =
                  let uu____6304 =
                    let uu____6319 =
                      let uu____6334 =
                        let uu____6349 =
                          let uu____6364 =
                            let uu____6379 =
                              let uu____6394 =
                                let uu____6409 =
                                  let uu____6424 =
                                    let uu____6439 =
                                      let uu____6454 =
                                        let uu____6469 =
                                          let uu____6484 =
                                            let uu____6499 =
                                              let uu____6514 =
                                                let uu____6527 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____6527,
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
                                              let uu____6534 =
                                                let uu____6549 =
                                                  let uu____6562 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____6562,
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
                                                let uu____6569 =
                                                  let uu____6584 =
                                                    let uu____6599 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____6599,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____6608 =
                                                    let uu____6625 =
                                                      let uu____6640 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____6640,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    let uu____6649 =
                                                      let uu____6666 =
                                                        let uu____6685 =
                                                          FStar_Parser_Const.p2l
                                                            ["FStar";
                                                            "Range";
                                                            "prims_to_fstar_range"]
                                                           in
                                                        (uu____6685,
                                                          (Prims.parse_int "1"),
                                                          idstep)
                                                         in
                                                      [uu____6666]  in
                                                    uu____6625 :: uu____6649
                                                     in
                                                  uu____6584 :: uu____6608
                                                   in
                                                uu____6549 :: uu____6569  in
                                              uu____6514 :: uu____6534  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6499
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6484
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
                                          :: uu____6469
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
                                        :: uu____6454
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
                                      :: uu____6439
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
                                                        let uu____6902 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____6902 y)) a466
                                                a467 a468)))
                                    :: uu____6424
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6409
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6394
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6379
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6364
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6349
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6334
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
                                          let uu____7069 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed_bool
                                            r uu____7069)) a470 a471 a472)))
                      :: uu____6319
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
                                        let uu____7095 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed_bool r
                                          uu____7095)) a474 a475 a476)))
                    :: uu____6304
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
                                      let uu____7121 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed_bool r
                                        uu____7121)) a478 a479 a480)))
                  :: uu____6289
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
                                    let uu____7147 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed_bool r
                                      uu____7147)) a482 a483 a484)))
                :: uu____6274
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6259
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6244
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6229
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6214
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6199
     in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c = FStar_Syntax_Embeddings.embed_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7300 =
        let uu____7301 =
          let uu____7302 = FStar_Syntax_Syntax.as_arg c  in [uu____7302]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7301  in
      uu____7300 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7352 =
                let uu____7365 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7365, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a485  -> (Obj.magic arg_as_bounded_int) a485)
                     (fun a486  ->
                        fun a487  ->
                          fun a488  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7381  ->
                                    fun uu____7382  ->
                                      match (uu____7381, uu____7382) with
                                      | ((int_to_t1,x),(uu____7401,y)) ->
                                          let uu____7411 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7411)) a486 a487 a488)))
                 in
              let uu____7412 =
                let uu____7427 =
                  let uu____7440 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7440, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a489  -> (Obj.magic arg_as_bounded_int) a489)
                       (fun a490  ->
                          fun a491  ->
                            fun a492  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7456  ->
                                      fun uu____7457  ->
                                        match (uu____7456, uu____7457) with
                                        | ((int_to_t1,x),(uu____7476,y)) ->
                                            let uu____7486 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7486)) a490 a491 a492)))
                   in
                let uu____7487 =
                  let uu____7502 =
                    let uu____7515 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____7515, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a493  -> (Obj.magic arg_as_bounded_int) a493)
                         (fun a494  ->
                            fun a495  ->
                              fun a496  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7531  ->
                                        fun uu____7532  ->
                                          match (uu____7531, uu____7532) with
                                          | ((int_to_t1,x),(uu____7551,y)) ->
                                              let uu____7561 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____7561)) a494 a495 a496)))
                     in
                  let uu____7562 =
                    let uu____7577 =
                      let uu____7590 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____7590, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a497  -> (Obj.magic arg_as_bounded_int) a497)
                           (fun a498  ->
                              fun a499  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7602  ->
                                        match uu____7602 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed_int
                                              r x)) a498 a499)))
                       in
                    [uu____7577]  in
                  uu____7502 :: uu____7562  in
                uu____7427 :: uu____7487  in
              uu____7352 :: uu____7412))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____7716 =
                let uu____7729 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____7729, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a500  -> (Obj.magic arg_as_bounded_int) a500)
                     (fun a501  ->
                        fun a502  ->
                          fun a503  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7745  ->
                                    fun uu____7746  ->
                                      match (uu____7745, uu____7746) with
                                      | ((int_to_t1,x),(uu____7765,y)) ->
                                          let uu____7775 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7775)) a501 a502 a503)))
                 in
              let uu____7776 =
                let uu____7791 =
                  let uu____7804 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____7804, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a504  -> (Obj.magic arg_as_bounded_int) a504)
                       (fun a505  ->
                          fun a506  ->
                            fun a507  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7820  ->
                                      fun uu____7821  ->
                                        match (uu____7820, uu____7821) with
                                        | ((int_to_t1,x),(uu____7840,y)) ->
                                            let uu____7850 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7850)) a505 a506 a507)))
                   in
                [uu____7791]  in
              uu____7716 :: uu____7776))
       in
    FStar_List.append add_sub_mul_v div_mod_unsigned  in
  let uu____7899 =
    FStar_List.map as_primitive_step
      (FStar_List.append basic_ops bounded_arith_ops)
     in
  FStar_All.pipe_left prim_from_list uu____7899 
let (equality_ops : primitive_step FStar_Util.psmap) =
  let interp_prop psc args =
    let r = psc.psc_range  in
    match args with
    | (_typ,uu____7947)::(a1,uu____7949)::(a2,uu____7951)::[] ->
        let uu____7988 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____7988 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___136_7994 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___136_7994.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___136_7994.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___137_7998 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___137_7998.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___137_7998.FStar_Syntax_Syntax.vars)
                })
         | uu____7999 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8001)::uu____8002::(a1,uu____8004)::(a2,uu____8006)::[] ->
        let uu____8055 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8055 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___136_8061 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___136_8061.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___136_8061.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___137_8065 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___137_8065.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___137_8065.FStar_Syntax_Syntax.vars)
                })
         | uu____8066 -> FStar_Pervasives_Native.None)
    | uu____8067 -> failwith "Unexpected number of arguments"  in
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
    let uu____8079 =
      let uu____8080 = FStar_Syntax_Subst.compress t  in
      uu____8080.FStar_Syntax_Syntax.n  in
    match uu____8079 with
    | FStar_Syntax_Syntax.Tm_lazy i when
        i.FStar_Syntax_Syntax.kind = FStar_Syntax_Syntax.Lazy_binder ->
        let uu____8086 = FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob  in
        FStar_Pervasives_Native.Some uu____8086
    | uu____8087 -> FStar_Pervasives_Native.None
  
let mk_psc_subst :
  'Auu____8091 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8091) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8151  ->
           fun subst1  ->
             match uu____8151 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8192,uu____8193)) ->
                      let uu____8252 = b  in
                      (match uu____8252 with
                       | (bv,uu____8260) ->
                           let uu____8261 =
                             let uu____8262 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____8262  in
                           if uu____8261
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8267 = unembed_binder term1  in
                              match uu____8267 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8274 =
                                      let uu___138_8275 = bv  in
                                      let uu____8276 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___138_8275.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___138_8275.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8276
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8274
                                     in
                                  let b_for_x =
                                    let uu____8280 =
                                      let uu____8287 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8287)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8280  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___83_8296  ->
                                         match uu___83_8296 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8297,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8299;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8300;_})
                                             ->
                                             Prims.op_Negation
                                               (FStar_Ident.ident_equals
                                                  b1.FStar_Syntax_Syntax.ppname
                                                  b'.FStar_Syntax_Syntax.ppname)
                                         | uu____8305 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8306 -> subst1)) env []
  
let reduce_primops :
  'Auu____8323 'Auu____8324 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8323) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8324 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8366 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8366 with
             | (head1,args) ->
                 let uu____8403 =
                   let uu____8404 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8404.FStar_Syntax_Syntax.n  in
                 (match uu____8403 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8408 =
                        FStar_Util.psmap_try_find cfg.primitive_steps
                          (FStar_Ident.text_of_lid
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                         in
                      (match uu____8408 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           if (FStar_List.length args) < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8423  ->
                                   let uu____8424 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____8425 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length args)
                                      in
                                   let uu____8432 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8424 uu____8425 uu____8432);
                              tm)
                           else
                             (log_primops cfg
                                (fun uu____8437  ->
                                   let uu____8438 =
                                     FStar_Syntax_Print.term_to_string tm  in
                                   FStar_Util.print1
                                     "primop: trying to reduce <%s>\n"
                                     uu____8438);
                              (let psc =
                                 {
                                   psc_range =
                                     (head1.FStar_Syntax_Syntax.pos);
                                   psc_subst =
                                     (fun uu____8441  ->
                                        if
                                          prim_step.requires_binder_substitution
                                        then mk_psc_subst cfg env
                                        else [])
                                 }  in
                               let uu____8443 =
                                 prim_step.interpretation psc args  in
                               match uu____8443 with
                               | FStar_Pervasives_Native.None  ->
                                   (log_primops cfg
                                      (fun uu____8449  ->
                                         let uu____8450 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         FStar_Util.print1
                                           "primop: <%s> did not reduce\n"
                                           uu____8450);
                                    tm)
                               | FStar_Pervasives_Native.Some reduced ->
                                   (log_primops cfg
                                      (fun uu____8456  ->
                                         let uu____8457 =
                                           FStar_Syntax_Print.term_to_string
                                             tm
                                            in
                                         let uu____8458 =
                                           FStar_Syntax_Print.term_to_string
                                             reduced
                                            in
                                         FStar_Util.print2
                                           "primop: <%s> reduced to <%s>\n"
                                           uu____8457 uu____8458);
                                    reduced)))
                       | FStar_Pervasives_Native.Some uu____8459 ->
                           (log_primops cfg
                              (fun uu____8463  ->
                                 let uu____8464 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8464);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8468  ->
                            let uu____8469 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8469);
                       (match args with
                        | (a1,uu____8471)::[] ->
                            FStar_Syntax_Embeddings.embed_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8488 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8500  ->
                            let uu____8501 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8501);
                       (match args with
                        | (t,uu____8503)::(r,uu____8505)::[] ->
                            let uu____8532 =
                              FStar_Syntax_Embeddings.unembed_range r  in
                            (match uu____8532 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___139_8536 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___139_8536.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___139_8536.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____8539 -> tm))
                  | uu____8548 -> tm))
  
let reduce_equality :
  'Auu____8553 'Auu____8554 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8553) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8554 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___140_8592 = cfg  in
         {
           steps =
             (let uu___141_8595 = default_steps  in
              {
                beta = (uu___141_8595.beta);
                iota = (uu___141_8595.iota);
                zeta = (uu___141_8595.zeta);
                weak = (uu___141_8595.weak);
                hnf = (uu___141_8595.hnf);
                primops = true;
                no_delta_steps = (uu___141_8595.no_delta_steps);
                unfold_until = (uu___141_8595.unfold_until);
                unfold_only = (uu___141_8595.unfold_only);
                unfold_attr = (uu___141_8595.unfold_attr);
                unfold_tac = (uu___141_8595.unfold_tac);
                pure_subterms_within_computations =
                  (uu___141_8595.pure_subterms_within_computations);
                simplify = (uu___141_8595.simplify);
                erase_universes = (uu___141_8595.erase_universes);
                allow_unbound_universes =
                  (uu___141_8595.allow_unbound_universes);
                reify_ = (uu___141_8595.reify_);
                compress_uvars = (uu___141_8595.compress_uvars);
                no_full_norm = (uu___141_8595.no_full_norm);
                check_no_uvars = (uu___141_8595.check_no_uvars);
                unmeta = (uu___141_8595.unmeta);
                unascribe = (uu___141_8595.unascribe)
              });
           tcenv = (uu___140_8592.tcenv);
           debug = (uu___140_8592.debug);
           delta_level = (uu___140_8592.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___140_8592.strong);
           memoize_lazy = (uu___140_8592.memoize_lazy);
           normalize_pure_lets = (uu___140_8592.normalize_pure_lets)
         }) tm
  
let maybe_simplify_aux :
  'Auu____8602 'Auu____8603 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8602) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8603 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____8645 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____8645
          then tm1
          else
            (let w t =
               let uu___142_8657 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___142_8657.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___142_8657.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_meta
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                      FStar_Syntax_Syntax.pos = uu____8673;
                      FStar_Syntax_Syntax.vars = uu____8674;_},uu____8675)
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
                      FStar_Syntax_Syntax.pos = uu____8682;
                      FStar_Syntax_Syntax.vars = uu____8683;_},uu____8684)
                   when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____8690 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____8695 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____8695
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____8716 =
                 match uu____8716 with
                 | (t1,q) ->
                     let uu____8729 = FStar_Syntax_Util.is_auto_squash t1  in
                     (match uu____8729 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____8757 -> (t1, q))
                  in
               let uu____8766 = FStar_Syntax_Util.head_and_args t  in
               match uu____8766 with
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
                         FStar_Syntax_Syntax.pos = uu____8863;
                         FStar_Syntax_Syntax.vars = uu____8864;_},uu____8865);
                    FStar_Syntax_Syntax.pos = uu____8866;
                    FStar_Syntax_Syntax.vars = uu____8867;_},args)
                 ->
                 let uu____8893 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____8893
                 then
                   let uu____8894 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____8894 with
                    | (FStar_Pervasives_Native.Some (true ),uu____8949)::
                        (uu____8950,(arg,uu____8952))::[] ->
                        maybe_auto_squash arg
                    | (uu____9017,(arg,uu____9019))::(FStar_Pervasives_Native.Some
                                                      (true ),uu____9020)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____9085)::uu____9086::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9149::(FStar_Pervasives_Native.Some (false
                                   ),uu____9150)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____9213 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____9229 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____9229
                    then
                      let uu____9230 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____9230 with
                      | (FStar_Pervasives_Native.Some (true ),uu____9285)::uu____9286::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____9349::(FStar_Pervasives_Native.Some (true
                                     ),uu____9350)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____9413)::
                          (uu____9414,(arg,uu____9416))::[] ->
                          maybe_auto_squash arg
                      | (uu____9481,(arg,uu____9483))::(FStar_Pervasives_Native.Some
                                                        (false ),uu____9484)::[]
                          -> maybe_auto_squash arg
                      | uu____9549 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____9565 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____9565
                       then
                         let uu____9566 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____9566 with
                         | uu____9621::(FStar_Pervasives_Native.Some (true
                                        ),uu____9622)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false ),uu____9685)::uu____9686::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____9749)::
                             (uu____9750,(arg,uu____9752))::[] ->
                             maybe_auto_squash arg
                         | (uu____9817,(p,uu____9819))::(uu____9820,(q,uu____9822))::[]
                             ->
                             let uu____9887 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____9887
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____9889 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____9905 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.iff_lid
                             in
                          if uu____9905
                          then
                            let uu____9906 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____9906 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____9961)::(FStar_Pervasives_Native.Some
                                               (true ),uu____9962)::[]
                                -> w FStar_Syntax_Util.t_true
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10027)::(FStar_Pervasives_Native.Some
                                                (false ),uu____10028)::[]
                                -> w FStar_Syntax_Util.t_true
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10093)::(FStar_Pervasives_Native.Some
                                                (false ),uu____10094)::[]
                                -> w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____10159)::(FStar_Pervasives_Native.Some
                                                (true ),uu____10160)::[]
                                -> w FStar_Syntax_Util.t_false
                            | (uu____10225,(arg,uu____10227))::(FStar_Pervasives_Native.Some
                                                                (true
                                                                ),uu____10228)::[]
                                -> maybe_auto_squash arg
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____10293)::(uu____10294,(arg,uu____10296))::[]
                                -> maybe_auto_squash arg
                            | (uu____10361,(p,uu____10363))::(uu____10364,
                                                              (q,uu____10366))::[]
                                ->
                                let uu____10431 =
                                  FStar_Syntax_Util.term_eq p q  in
                                (if uu____10431
                                 then w FStar_Syntax_Util.t_true
                                 else squashed_head_un_auto_squash_args tm1)
                            | uu____10433 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____10449 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.not_lid
                                in
                             if uu____10449
                             then
                               let uu____10450 =
                                 FStar_All.pipe_right args
                                   (FStar_List.map simplify1)
                                  in
                               match uu____10450 with
                               | (FStar_Pervasives_Native.Some (true
                                  ),uu____10505)::[] ->
                                   w FStar_Syntax_Util.t_false
                               | (FStar_Pervasives_Native.Some (false
                                  ),uu____10544)::[] ->
                                   w FStar_Syntax_Util.t_true
                               | uu____10583 ->
                                   squashed_head_un_auto_squash_args tm1
                             else
                               (let uu____10599 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.forall_lid
                                   in
                                if uu____10599
                                then
                                  match args with
                                  | (t,uu____10601)::[] ->
                                      let uu____10618 =
                                        let uu____10619 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10619.FStar_Syntax_Syntax.n  in
                                      (match uu____10618 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10622::[],body,uu____10624)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (true ) ->
                                                w FStar_Syntax_Util.t_true
                                            | uu____10651 -> tm1)
                                       | uu____10654 -> tm1)
                                  | (uu____10655,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____10656))::(t,uu____10658)::[] ->
                                      let uu____10697 =
                                        let uu____10698 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____10698.FStar_Syntax_Syntax.n  in
                                      (match uu____10697 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____10701::[],body,uu____10703)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (true ) ->
                                                w FStar_Syntax_Util.t_true
                                            | uu____10730 -> tm1)
                                       | uu____10733 -> tm1)
                                  | uu____10734 -> tm1
                                else
                                  (let uu____10744 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.exists_lid
                                      in
                                   if uu____10744
                                   then
                                     match args with
                                     | (t,uu____10746)::[] ->
                                         let uu____10763 =
                                           let uu____10764 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____10764.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____10763 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (uu____10767::[],body,uu____10769)
                                              ->
                                              (match simp_t body with
                                               | FStar_Pervasives_Native.Some
                                                   (false ) ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____10796 -> tm1)
                                          | uu____10799 -> tm1)
                                     | (uu____10800,FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit
                                        uu____10801))::(t,uu____10803)::[] ->
                                         let uu____10842 =
                                           let uu____10843 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____10843.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____10842 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (uu____10846::[],body,uu____10848)
                                              ->
                                              (match simp_t body with
                                               | FStar_Pervasives_Native.Some
                                                   (false ) ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____10875 -> tm1)
                                          | uu____10878 -> tm1)
                                     | uu____10879 -> tm1
                                   else
                                     (let uu____10889 =
                                        FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.b2t_lid
                                         in
                                      if uu____10889
                                      then
                                        match args with
                                        | ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_constant
                                               (FStar_Const.Const_bool (true
                                               ));
                                             FStar_Syntax_Syntax.pos =
                                               uu____10890;
                                             FStar_Syntax_Syntax.vars =
                                               uu____10891;_},uu____10892)::[]
                                            -> w FStar_Syntax_Util.t_true
                                        | ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_constant
                                               (FStar_Const.Const_bool (false
                                               ));
                                             FStar_Syntax_Syntax.pos =
                                               uu____10909;
                                             FStar_Syntax_Syntax.vars =
                                               uu____10910;_},uu____10911)::[]
                                            -> w FStar_Syntax_Util.t_false
                                        | uu____10928 -> tm1
                                      else
                                        (let uu____10938 =
                                           FStar_Syntax_Util.is_auto_squash
                                             tm1
                                            in
                                         match uu____10938 with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.U_zero ,t)
                                             when
                                             FStar_Syntax_Util.is_sub_singleton
                                               t
                                             -> t
                                         | uu____10958 ->
                                             reduce_equality cfg env stack
                                               tm1))))))))
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____10968;
                    FStar_Syntax_Syntax.vars = uu____10969;_},args)
                 ->
                 let uu____10991 =
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.and_lid
                    in
                 if uu____10991
                 then
                   let uu____10992 =
                     FStar_All.pipe_right args (FStar_List.map simplify1)  in
                   (match uu____10992 with
                    | (FStar_Pervasives_Native.Some (true ),uu____11047)::
                        (uu____11048,(arg,uu____11050))::[] ->
                        maybe_auto_squash arg
                    | (uu____11115,(arg,uu____11117))::(FStar_Pervasives_Native.Some
                                                        (true ),uu____11118)::[]
                        -> maybe_auto_squash arg
                    | (FStar_Pervasives_Native.Some (false ),uu____11183)::uu____11184::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____11247::(FStar_Pervasives_Native.Some (false
                                    ),uu____11248)::[]
                        -> w FStar_Syntax_Util.t_false
                    | uu____11311 -> squashed_head_un_auto_squash_args tm1)
                 else
                   (let uu____11327 =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.or_lid
                       in
                    if uu____11327
                    then
                      let uu____11328 =
                        FStar_All.pipe_right args (FStar_List.map simplify1)
                         in
                      match uu____11328 with
                      | (FStar_Pervasives_Native.Some (true ),uu____11383)::uu____11384::[]
                          -> w FStar_Syntax_Util.t_true
                      | uu____11447::(FStar_Pervasives_Native.Some (true
                                      ),uu____11448)::[]
                          -> w FStar_Syntax_Util.t_true
                      | (FStar_Pervasives_Native.Some (false ),uu____11511)::
                          (uu____11512,(arg,uu____11514))::[] ->
                          maybe_auto_squash arg
                      | (uu____11579,(arg,uu____11581))::(FStar_Pervasives_Native.Some
                                                          (false
                                                          ),uu____11582)::[]
                          -> maybe_auto_squash arg
                      | uu____11647 -> squashed_head_un_auto_squash_args tm1
                    else
                      (let uu____11663 =
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.imp_lid
                          in
                       if uu____11663
                       then
                         let uu____11664 =
                           FStar_All.pipe_right args
                             (FStar_List.map simplify1)
                            in
                         match uu____11664 with
                         | uu____11719::(FStar_Pervasives_Native.Some (true
                                         ),uu____11720)::[]
                             -> w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____11783)::uu____11784::[] ->
                             w FStar_Syntax_Util.t_true
                         | (FStar_Pervasives_Native.Some (true ),uu____11847)::
                             (uu____11848,(arg,uu____11850))::[] ->
                             maybe_auto_squash arg
                         | (uu____11915,(p,uu____11917))::(uu____11918,
                                                           (q,uu____11920))::[]
                             ->
                             let uu____11985 = FStar_Syntax_Util.term_eq p q
                                in
                             (if uu____11985
                              then w FStar_Syntax_Util.t_true
                              else squashed_head_un_auto_squash_args tm1)
                         | uu____11987 ->
                             squashed_head_un_auto_squash_args tm1
                       else
                         (let uu____12003 =
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.iff_lid
                             in
                          if uu____12003
                          then
                            let uu____12004 =
                              FStar_All.pipe_right args
                                (FStar_List.map simplify1)
                               in
                            match uu____12004 with
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____12059)::(FStar_Pervasives_Native.Some
                                                (true ),uu____12060)::[]
                                -> w FStar_Syntax_Util.t_true
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____12125)::(FStar_Pervasives_Native.Some
                                                (false ),uu____12126)::[]
                                -> w FStar_Syntax_Util.t_true
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____12191)::(FStar_Pervasives_Native.Some
                                                (false ),uu____12192)::[]
                                -> w FStar_Syntax_Util.t_false
                            | (FStar_Pervasives_Native.Some (false
                               ),uu____12257)::(FStar_Pervasives_Native.Some
                                                (true ),uu____12258)::[]
                                -> w FStar_Syntax_Util.t_false
                            | (uu____12323,(arg,uu____12325))::(FStar_Pervasives_Native.Some
                                                                (true
                                                                ),uu____12326)::[]
                                -> maybe_auto_squash arg
                            | (FStar_Pervasives_Native.Some (true
                               ),uu____12391)::(uu____12392,(arg,uu____12394))::[]
                                -> maybe_auto_squash arg
                            | (uu____12459,(p,uu____12461))::(uu____12462,
                                                              (q,uu____12464))::[]
                                ->
                                let uu____12529 =
                                  FStar_Syntax_Util.term_eq p q  in
                                (if uu____12529
                                 then w FStar_Syntax_Util.t_true
                                 else squashed_head_un_auto_squash_args tm1)
                            | uu____12531 ->
                                squashed_head_un_auto_squash_args tm1
                          else
                            (let uu____12547 =
                               FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.not_lid
                                in
                             if uu____12547
                             then
                               let uu____12548 =
                                 FStar_All.pipe_right args
                                   (FStar_List.map simplify1)
                                  in
                               match uu____12548 with
                               | (FStar_Pervasives_Native.Some (true
                                  ),uu____12603)::[] ->
                                   w FStar_Syntax_Util.t_false
                               | (FStar_Pervasives_Native.Some (false
                                  ),uu____12642)::[] ->
                                   w FStar_Syntax_Util.t_true
                               | uu____12681 ->
                                   squashed_head_un_auto_squash_args tm1
                             else
                               (let uu____12697 =
                                  FStar_Syntax_Syntax.fv_eq_lid fv
                                    FStar_Parser_Const.forall_lid
                                   in
                                if uu____12697
                                then
                                  match args with
                                  | (t,uu____12699)::[] ->
                                      let uu____12716 =
                                        let uu____12717 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____12717.FStar_Syntax_Syntax.n  in
                                      (match uu____12716 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____12720::[],body,uu____12722)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (true ) ->
                                                w FStar_Syntax_Util.t_true
                                            | uu____12749 -> tm1)
                                       | uu____12752 -> tm1)
                                  | (uu____12753,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit
                                     uu____12754))::(t,uu____12756)::[] ->
                                      let uu____12795 =
                                        let uu____12796 =
                                          FStar_Syntax_Subst.compress t  in
                                        uu____12796.FStar_Syntax_Syntax.n  in
                                      (match uu____12795 with
                                       | FStar_Syntax_Syntax.Tm_abs
                                           (uu____12799::[],body,uu____12801)
                                           ->
                                           (match simp_t body with
                                            | FStar_Pervasives_Native.Some
                                                (true ) ->
                                                w FStar_Syntax_Util.t_true
                                            | uu____12828 -> tm1)
                                       | uu____12831 -> tm1)
                                  | uu____12832 -> tm1
                                else
                                  (let uu____12842 =
                                     FStar_Syntax_Syntax.fv_eq_lid fv
                                       FStar_Parser_Const.exists_lid
                                      in
                                   if uu____12842
                                   then
                                     match args with
                                     | (t,uu____12844)::[] ->
                                         let uu____12861 =
                                           let uu____12862 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____12862.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____12861 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (uu____12865::[],body,uu____12867)
                                              ->
                                              (match simp_t body with
                                               | FStar_Pervasives_Native.Some
                                                   (false ) ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____12894 -> tm1)
                                          | uu____12897 -> tm1)
                                     | (uu____12898,FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit
                                        uu____12899))::(t,uu____12901)::[] ->
                                         let uu____12940 =
                                           let uu____12941 =
                                             FStar_Syntax_Subst.compress t
                                              in
                                           uu____12941.FStar_Syntax_Syntax.n
                                            in
                                         (match uu____12940 with
                                          | FStar_Syntax_Syntax.Tm_abs
                                              (uu____12944::[],body,uu____12946)
                                              ->
                                              (match simp_t body with
                                               | FStar_Pervasives_Native.Some
                                                   (false ) ->
                                                   w
                                                     FStar_Syntax_Util.t_false
                                               | uu____12973 -> tm1)
                                          | uu____12976 -> tm1)
                                     | uu____12977 -> tm1
                                   else
                                     (let uu____12987 =
                                        FStar_Syntax_Syntax.fv_eq_lid fv
                                          FStar_Parser_Const.b2t_lid
                                         in
                                      if uu____12987
                                      then
                                        match args with
                                        | ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_constant
                                               (FStar_Const.Const_bool (true
                                               ));
                                             FStar_Syntax_Syntax.pos =
                                               uu____12988;
                                             FStar_Syntax_Syntax.vars =
                                               uu____12989;_},uu____12990)::[]
                                            -> w FStar_Syntax_Util.t_true
                                        | ({
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_constant
                                               (FStar_Const.Const_bool (false
                                               ));
                                             FStar_Syntax_Syntax.pos =
                                               uu____13007;
                                             FStar_Syntax_Syntax.vars =
                                               uu____13008;_},uu____13009)::[]
                                            -> w FStar_Syntax_Util.t_false
                                        | uu____13026 -> tm1
                                      else
                                        (let uu____13036 =
                                           FStar_Syntax_Util.is_auto_squash
                                             tm1
                                            in
                                         match uu____13036 with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.U_zero ,t)
                                             when
                                             FStar_Syntax_Util.is_sub_singleton
                                               t
                                             -> t
                                         | uu____13056 ->
                                             reduce_equality cfg env stack
                                               tm1))))))))
             | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                 (match simp_t t with
                  | FStar_Pervasives_Native.Some (true ) ->
                      bv.FStar_Syntax_Syntax.sort
                  | FStar_Pervasives_Native.Some (false ) -> tm1
                  | FStar_Pervasives_Native.None  -> tm1)
             | uu____13071 -> tm1)
  
let maybe_simplify :
  'Auu____13078 'Auu____13079 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____13078) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____13079 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.debug).b380
          then
            (let uu____13122 = FStar_Syntax_Print.term_to_string tm  in
             let uu____13123 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____13122
               uu____13123)
          else ();
          tm'
  
let is_norm_request :
  'Auu____13129 .
    FStar_Syntax_Syntax.term -> 'Auu____13129 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____13142 =
        let uu____13149 =
          let uu____13150 = FStar_Syntax_Util.un_uinst hd1  in
          uu____13150.FStar_Syntax_Syntax.n  in
        (uu____13149, args)  in
      match uu____13142 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____13156::uu____13157::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____13161::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____13166::uu____13167::[])
          -> FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____13170 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___84_13181  ->
    match uu___84_13181 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____13187 =
          let uu____13190 =
            let uu____13191 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            UnfoldOnly uu____13191  in
          [uu____13190]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____13187
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____13207 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____13207) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        try
          let uu____13260 =
            let uu____13263 =
              let uu____13266 =
                let uu____13271 =
                  FStar_Syntax_Embeddings.unembed_list_safe
                    FStar_Syntax_Embeddings.unembed_norm_step
                   in
                uu____13271 s  in
              FStar_All.pipe_right uu____13266 FStar_Util.must  in
            FStar_All.pipe_right uu____13263 tr_norm_steps  in
          FStar_Pervasives_Native.Some uu____13260
        with | uu____13299 -> FStar_Pervasives_Native.None  in
      match args with
      | uu____13310::(tm,uu____13312)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____13341)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____13362)::uu____13363::(tm,uu____13365)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____13402 =
            let uu____13407 = full_norm steps  in parse_steps uu____13407  in
          (match uu____13402 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____13446 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___85_13463  ->
    match uu___85_13463 with
    | (App
        (uu____13466,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____13467;
                       FStar_Syntax_Syntax.vars = uu____13468;_},uu____13469,uu____13470))::uu____13471
        -> true
    | uu____13478 -> false
  
let firstn :
  'Auu____13484 .
    Prims.int ->
      'Auu____13484 Prims.list ->
        ('Auu____13484 Prims.list,'Auu____13484 Prims.list)
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
          (uu____13520,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____13521;
                         FStar_Syntax_Syntax.vars = uu____13522;_},uu____13523,uu____13524))::uu____13525
          -> (cfg.steps).reify_
      | uu____13532 -> false
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____13676 ->
                   let uu____13701 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____13701
               | uu____13702 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____13710  ->
               let uu____13711 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____13712 = FStar_Syntax_Print.term_to_string t1  in
               let uu____13713 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____13720 =
                 let uu____13721 =
                   let uu____13724 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____13724
                    in
                 stack_to_string uu____13721  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____13711 uu____13712 uu____13713 uu____13720);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____13747 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____13748 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____13749 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13750;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____13751;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13754;
                 FStar_Syntax_Syntax.fv_delta = uu____13755;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____13756;
                 FStar_Syntax_Syntax.fv_delta = uu____13757;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____13758);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_meta
               (t0,FStar_Syntax_Syntax.Meta_quoted (t11,qi)) ->
               let t01 = closure_as_term cfg env t0  in
               let t12 =
                 if qi.FStar_Syntax_Syntax.qopen
                 then closure_as_term cfg env t11
                 else t11  in
               let t2 =
                 let uu___145_13782 = t1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_meta
                        (t01, (FStar_Syntax_Syntax.Meta_quoted (t12, qi))));
                   FStar_Syntax_Syntax.pos =
                     (uu___145_13782.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___145_13782.FStar_Syntax_Syntax.vars)
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
                 let uu___146_13812 = cfg  in
                 {
                   steps =
                     (let uu___147_13815 = cfg.steps  in
                      {
                        beta = (uu___147_13815.beta);
                        iota = (uu___147_13815.iota);
                        zeta = (uu___147_13815.zeta);
                        weak = (uu___147_13815.weak);
                        hnf = (uu___147_13815.hnf);
                        primops = (uu___147_13815.primops);
                        no_delta_steps = false;
                        unfold_until = (uu___147_13815.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___147_13815.unfold_attr);
                        unfold_tac = (uu___147_13815.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___147_13815.pure_subterms_within_computations);
                        simplify = (uu___147_13815.simplify);
                        erase_universes = (uu___147_13815.erase_universes);
                        allow_unbound_universes =
                          (uu___147_13815.allow_unbound_universes);
                        reify_ = (uu___147_13815.reify_);
                        compress_uvars = (uu___147_13815.compress_uvars);
                        no_full_norm = (uu___147_13815.no_full_norm);
                        check_no_uvars = (uu___147_13815.check_no_uvars);
                        unmeta = (uu___147_13815.unmeta);
                        unascribe = (uu___147_13815.unascribe)
                      });
                   tcenv = (uu___146_13812.tcenv);
                   debug = (uu___146_13812.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___146_13812.primitive_steps);
                   strong = (uu___146_13812.strong);
                   memoize_lazy = (uu___146_13812.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____13818 = get_norm_request (norm cfg' env []) args  in
               (match uu____13818 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____13849  ->
                              fun stack1  ->
                                match uu____13849 with
                                | (a,aq) ->
                                    let uu____13861 =
                                      let uu____13862 =
                                        let uu____13869 =
                                          let uu____13870 =
                                            let uu____13901 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____13901, false)  in
                                          Clos uu____13870  in
                                        (uu____13869, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____13862  in
                                    uu____13861 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____13985  ->
                          let uu____13986 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____13986);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____14008 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___86_14013  ->
                                match uu___86_14013 with
                                | UnfoldUntil uu____14014 -> true
                                | UnfoldOnly uu____14015 -> true
                                | uu____14018 -> false))
                         in
                      if uu____14008
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___148_14023 = cfg  in
                      let uu____14024 = to_fsteps s  in
                      {
                        steps = uu____14024;
                        tcenv = (uu___148_14023.tcenv);
                        debug = (uu___148_14023.debug);
                        delta_level;
                        primitive_steps = (uu___148_14023.primitive_steps);
                        strong = (uu___148_14023.strong);
                        memoize_lazy = (uu___148_14023.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____14033 =
                          let uu____14034 =
                            let uu____14039 = FStar_Util.now ()  in
                            (t1, uu____14039)  in
                          Debug uu____14034  in
                        uu____14033 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____14043 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____14043
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____14052 =
                      let uu____14059 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____14059, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____14052  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____14069 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____14069  in
               let uu____14070 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____14070
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____14076  ->
                       let uu____14077 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____14078 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____14077 uu____14078);
                  if b
                  then
                    (let uu____14079 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____14079 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    FStar_All.pipe_right cfg.delta_level
                      (FStar_Util.for_some
                         (fun uu___87_14088  ->
                            match uu___87_14088 with
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
                          (let uu____14098 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____14098))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____14117) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____14152,uu____14153) -> false)))
                     in
                  log cfg
                    (fun uu____14175  ->
                       let uu____14176 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____14177 =
                         FStar_Range.string_of_range
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____14178 =
                         FStar_Util.string_of_bool should_delta1  in
                       FStar_Util.print3
                         ">>> For %s (%s), should_delta = %s\n" uu____14176
                         uu____14177 uu____14178);
                  if should_delta1
                  then do_unfold_fv cfg env stack t1 qninfo fv
                  else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____14181 = lookup_bvar env x  in
               (match uu____14181 with
                | Univ uu____14184 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____14233 = FStar_ST.op_Bang r  in
                      (match uu____14233 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____14351  ->
                                 let uu____14352 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____14353 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____14352
                                   uu____14353);
                            (let uu____14354 =
                               let uu____14355 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____14355.FStar_Syntax_Syntax.n  in
                             match uu____14354 with
                             | FStar_Syntax_Syntax.Tm_abs uu____14358 ->
                                 norm cfg env2 stack t'
                             | uu____14375 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____14445)::uu____14446 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____14455)::uu____14456 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____14466,uu____14467))::stack_rest ->
                    (match c with
                     | Univ uu____14471 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____14480 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____14501  ->
                                    let uu____14502 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14502);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____14542  ->
                                    let uu____14543 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____14543);
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
                       (fun uu____14621  ->
                          let uu____14622 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____14622);
                     norm cfg env stack1 t1)
                | (Debug uu____14623)::uu____14624 ->
                    if (cfg.steps).weak
                    then
                      let uu____14631 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14631
                    else
                      (let uu____14633 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14633 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14675  -> dummy :: env1) env)
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
                                          let uu____14712 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14712)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_14717 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_14717.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_14717.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14718 -> lopt  in
                           (log cfg
                              (fun uu____14724  ->
                                 let uu____14725 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14725);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_14734 = cfg  in
                               {
                                 steps = (uu___150_14734.steps);
                                 tcenv = (uu___150_14734.tcenv);
                                 debug = (uu___150_14734.debug);
                                 delta_level = (uu___150_14734.delta_level);
                                 primitive_steps =
                                   (uu___150_14734.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_14734.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_14734.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____14745)::uu____14746 ->
                    if (cfg.steps).weak
                    then
                      let uu____14753 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14753
                    else
                      (let uu____14755 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14755 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14797  -> dummy :: env1) env)
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
                                          let uu____14834 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14834)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_14839 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_14839.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_14839.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14840 -> lopt  in
                           (log cfg
                              (fun uu____14846  ->
                                 let uu____14847 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14847);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_14856 = cfg  in
                               {
                                 steps = (uu___150_14856.steps);
                                 tcenv = (uu___150_14856.tcenv);
                                 debug = (uu___150_14856.debug);
                                 delta_level = (uu___150_14856.delta_level);
                                 primitive_steps =
                                   (uu___150_14856.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_14856.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_14856.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____14867)::uu____14868 ->
                    if (cfg.steps).weak
                    then
                      let uu____14879 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____14879
                    else
                      (let uu____14881 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____14881 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____14923  -> dummy :: env1) env)
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
                                          let uu____14960 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____14960)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_14965 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_14965.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_14965.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____14966 -> lopt  in
                           (log cfg
                              (fun uu____14972  ->
                                 let uu____14973 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____14973);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_14982 = cfg  in
                               {
                                 steps = (uu___150_14982.steps);
                                 tcenv = (uu___150_14982.tcenv);
                                 debug = (uu___150_14982.debug);
                                 delta_level = (uu___150_14982.delta_level);
                                 primitive_steps =
                                   (uu___150_14982.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_14982.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_14982.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____14993)::uu____14994 ->
                    if (cfg.steps).weak
                    then
                      let uu____15005 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15005
                    else
                      (let uu____15007 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15007 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15049  -> dummy :: env1) env)
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
                                          let uu____15086 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15086)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_15091 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_15091.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_15091.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15092 -> lopt  in
                           (log cfg
                              (fun uu____15098  ->
                                 let uu____15099 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15099);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_15108 = cfg  in
                               {
                                 steps = (uu___150_15108.steps);
                                 tcenv = (uu___150_15108.tcenv);
                                 debug = (uu___150_15108.debug);
                                 delta_level = (uu___150_15108.delta_level);
                                 primitive_steps =
                                   (uu___150_15108.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_15108.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_15108.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____15119)::uu____15120 ->
                    if (cfg.steps).weak
                    then
                      let uu____15135 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15135
                    else
                      (let uu____15137 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15137 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15179  -> dummy :: env1) env)
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
                                          let uu____15216 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15216)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_15221 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_15221.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_15221.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15222 -> lopt  in
                           (log cfg
                              (fun uu____15228  ->
                                 let uu____15229 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15229);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_15238 = cfg  in
                               {
                                 steps = (uu___150_15238.steps);
                                 tcenv = (uu___150_15238.tcenv);
                                 debug = (uu___150_15238.debug);
                                 delta_level = (uu___150_15238.delta_level);
                                 primitive_steps =
                                   (uu___150_15238.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_15238.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_15238.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____15249 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15249
                    else
                      (let uu____15251 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____15251 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____15293  -> dummy :: env1) env)
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
                                          let uu____15330 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____15330)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_15335 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_15335.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_15335.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____15336 -> lopt  in
                           (log cfg
                              (fun uu____15342  ->
                                 let uu____15343 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____15343);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_15352 = cfg  in
                               {
                                 steps = (uu___150_15352.steps);
                                 tcenv = (uu___150_15352.tcenv);
                                 debug = (uu___150_15352.debug);
                                 delta_level = (uu___150_15352.delta_level);
                                 primitive_steps =
                                   (uu___150_15352.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_15352.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_15352.normalize_pure_lets)
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
                      (fun uu____15401  ->
                         fun stack1  ->
                           match uu____15401 with
                           | (a,aq) ->
                               let uu____15413 =
                                 let uu____15414 =
                                   let uu____15421 =
                                     let uu____15422 =
                                       let uu____15453 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____15453, false)  in
                                     Clos uu____15422  in
                                   (uu____15421, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____15414  in
                               uu____15413 :: stack1) args)
                  in
               (log cfg
                  (fun uu____15537  ->
                     let uu____15538 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____15538);
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
                             ((let uu___151_15574 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___151_15574.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___151_15574.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____15575 ->
                      let uu____15580 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____15580)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____15583 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____15583 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____15614 =
                          let uu____15615 =
                            let uu____15622 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___152_15624 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___152_15624.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___152_15624.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____15622)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____15615  in
                        mk uu____15614 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____15643 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____15643
               else
                 (let uu____15645 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____15645 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____15653 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____15677  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____15653 c1  in
                      let t2 =
                        let uu____15699 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____15699 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____15810)::uu____15811 ->
                    (log cfg
                       (fun uu____15822  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____15823)::uu____15824 ->
                    (log cfg
                       (fun uu____15835  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____15836,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____15837;
                                   FStar_Syntax_Syntax.vars = uu____15838;_},uu____15839,uu____15840))::uu____15841
                    ->
                    (log cfg
                       (fun uu____15850  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____15851)::uu____15852 ->
                    (log cfg
                       (fun uu____15863  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____15864 ->
                    (log cfg
                       (fun uu____15867  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____15871  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____15888 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____15888
                         | FStar_Util.Inr c ->
                             let uu____15896 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____15896
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____15909 =
                               let uu____15910 =
                                 let uu____15937 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____15937, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____15910
                                in
                             mk uu____15909 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____15956 ->
                           let uu____15957 =
                             let uu____15958 =
                               let uu____15959 =
                                 let uu____15986 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____15986, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____15959
                                in
                             mk uu____15958 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____15957))))
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
                         let uu____16096 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____16096 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___153_16116 = cfg  in
                               let uu____16117 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___153_16116.steps);
                                 tcenv = uu____16117;
                                 debug = (uu___153_16116.debug);
                                 delta_level = (uu___153_16116.delta_level);
                                 primitive_steps =
                                   (uu___153_16116.primitive_steps);
                                 strong = (uu___153_16116.strong);
                                 memoize_lazy = (uu___153_16116.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___153_16116.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____16122 =
                                 let uu____16123 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____16123  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____16122
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___154_16126 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___154_16126.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___154_16126.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___154_16126.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___154_16126.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____16127 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____16127
           | FStar_Syntax_Syntax.Tm_let
               ((uu____16138,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____16139;
                               FStar_Syntax_Syntax.lbunivs = uu____16140;
                               FStar_Syntax_Syntax.lbtyp = uu____16141;
                               FStar_Syntax_Syntax.lbeff = uu____16142;
                               FStar_Syntax_Syntax.lbdef = uu____16143;
                               FStar_Syntax_Syntax.lbattrs = uu____16144;
                               FStar_Syntax_Syntax.lbpos = uu____16145;_}::uu____16146),uu____16147)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____16187 =
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
               if uu____16187
               then
                 let binder =
                   let uu____16189 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____16189  in
                 let env1 =
                   let uu____16199 =
                     let uu____16206 =
                       let uu____16207 =
                         let uu____16238 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____16238,
                           false)
                          in
                       Clos uu____16207  in
                     ((FStar_Pervasives_Native.Some binder), uu____16206)  in
                   uu____16199 :: env  in
                 (log cfg
                    (fun uu____16331  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____16335  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____16336 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____16336))
                 else
                   (let uu____16338 =
                      let uu____16343 =
                        let uu____16344 =
                          let uu____16345 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____16345
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____16344]  in
                      FStar_Syntax_Subst.open_term uu____16343 body  in
                    match uu____16338 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____16354  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____16362 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____16362  in
                            FStar_Util.Inl
                              (let uu___155_16372 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___155_16372.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___155_16372.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____16375  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___156_16377 = lb  in
                             let uu____16378 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___156_16377.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___156_16377.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____16378;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___156_16377.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___156_16377.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____16413  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___157_16436 = cfg  in
                             {
                               steps = (uu___157_16436.steps);
                               tcenv = (uu___157_16436.tcenv);
                               debug = (uu___157_16436.debug);
                               delta_level = (uu___157_16436.delta_level);
                               primitive_steps =
                                 (uu___157_16436.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___157_16436.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___157_16436.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____16439  ->
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
               let uu____16456 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____16456 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____16492 =
                               let uu___158_16493 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___158_16493.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___158_16493.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____16492  in
                           let uu____16494 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____16494 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____16520 =
                                   FStar_List.map (fun uu____16536  -> dummy)
                                     lbs1
                                    in
                                 let uu____16537 =
                                   let uu____16546 =
                                     FStar_List.map
                                       (fun uu____16566  -> dummy) xs1
                                      in
                                   FStar_List.append uu____16546 env  in
                                 FStar_List.append uu____16520 uu____16537
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____16590 =
                                       let uu___159_16591 = rc  in
                                       let uu____16592 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___159_16591.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____16592;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___159_16591.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____16590
                                 | uu____16599 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___160_16603 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___160_16603.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___160_16603.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___160_16603.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___160_16603.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____16613 =
                        FStar_List.map (fun uu____16629  -> dummy) lbs2  in
                      FStar_List.append uu____16613 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____16637 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____16637 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___161_16653 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___161_16653.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___161_16653.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____16680 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____16680
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____16699 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____16775  ->
                        match uu____16775 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___162_16896 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___162_16896.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___162_16896.FStar_Syntax_Syntax.sort)
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
               (match uu____16699 with
                | (rec_env,memos,uu____17109) ->
                    let uu____17162 =
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
                             let uu____17473 =
                               let uu____17480 =
                                 let uu____17481 =
                                   let uu____17512 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____17512, false)
                                    in
                                 Clos uu____17481  in
                               (FStar_Pervasives_Native.None, uu____17480)
                                in
                             uu____17473 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____17622  ->
                     let uu____17623 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____17623);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | FStar_Syntax_Syntax.Meta_quoted (qt,inf) ->
                     rebuild cfg env stack t1
                 | uu____17651 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____17653::uu____17654 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____17659) ->
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
                             | uu____17682 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____17696 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____17696
                              | uu____17707 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____17711 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____17737 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____17755 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____17772 =
                        let uu____17773 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____17774 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____17773 uu____17774
                         in
                      failwith uu____17772
                    else rebuild cfg env stack t2
                | uu____17776 -> norm cfg env stack t2))

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
                let uu____17786 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____17786  in
              let uu____17787 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____17787 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____17800  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____17811  ->
                        let uu____17812 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____17813 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____17812 uu____17813);
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
                      | (UnivArgs (us',uu____17826))::stack1 ->
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
                      | uu____17881 when (cfg.steps).erase_universes ->
                          norm cfg env stack t1
                      | uu____17884 ->
                          let uu____17887 =
                            let uu____17888 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____17888
                             in
                          failwith uu____17887
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
                  let uu___163_17912 = cfg  in
                  let uu____17913 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____17913;
                    tcenv = (uu___163_17912.tcenv);
                    debug = (uu___163_17912.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___163_17912.primitive_steps);
                    strong = (uu___163_17912.strong);
                    memoize_lazy = (uu___163_17912.memoize_lazy);
                    normalize_pure_lets =
                      (uu___163_17912.normalize_pure_lets)
                  }
                else
                  (let uu___164_17915 = cfg  in
                   {
                     steps =
                       (let uu___165_17918 = cfg.steps  in
                        {
                          beta = (uu___165_17918.beta);
                          iota = (uu___165_17918.iota);
                          zeta = false;
                          weak = (uu___165_17918.weak);
                          hnf = (uu___165_17918.hnf);
                          primops = (uu___165_17918.primops);
                          no_delta_steps = (uu___165_17918.no_delta_steps);
                          unfold_until = (uu___165_17918.unfold_until);
                          unfold_only = (uu___165_17918.unfold_only);
                          unfold_attr = (uu___165_17918.unfold_attr);
                          unfold_tac = (uu___165_17918.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___165_17918.pure_subterms_within_computations);
                          simplify = (uu___165_17918.simplify);
                          erase_universes = (uu___165_17918.erase_universes);
                          allow_unbound_universes =
                            (uu___165_17918.allow_unbound_universes);
                          reify_ = (uu___165_17918.reify_);
                          compress_uvars = (uu___165_17918.compress_uvars);
                          no_full_norm = (uu___165_17918.no_full_norm);
                          check_no_uvars = (uu___165_17918.check_no_uvars);
                          unmeta = (uu___165_17918.unmeta);
                          unascribe = (uu___165_17918.unascribe)
                        });
                     tcenv = (uu___164_17915.tcenv);
                     debug = (uu___164_17915.debug);
                     delta_level = (uu___164_17915.delta_level);
                     primitive_steps = (uu___164_17915.primitive_steps);
                     strong = (uu___164_17915.strong);
                     memoize_lazy = (uu___164_17915.memoize_lazy);
                     normalize_pure_lets =
                       (uu___164_17915.normalize_pure_lets)
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
                  (fun uu____17948  ->
                     let uu____17949 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____17950 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____17949
                       uu____17950);
                (let uu____17951 =
                   let uu____17952 = FStar_Syntax_Subst.compress head2  in
                   uu____17952.FStar_Syntax_Syntax.n  in
                 match uu____17951 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____17970 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____17970
                        in
                     let uu____17971 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____17971 with
                      | (uu____17972,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____17978 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____17986 =
                                   let uu____17987 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____17987.FStar_Syntax_Syntax.n  in
                                 match uu____17986 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____17993,uu____17994))
                                     ->
                                     let uu____18003 =
                                       let uu____18004 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____18004.FStar_Syntax_Syntax.n  in
                                     (match uu____18003 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____18010,msrc,uu____18012))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____18021 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____18021
                                      | uu____18022 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____18023 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____18024 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____18024 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___166_18029 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___166_18029.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___166_18029.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___166_18029.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___166_18029.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___166_18029.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____18030 = FStar_List.tl stack  in
                                    let uu____18031 =
                                      let uu____18032 =
                                        let uu____18035 =
                                          let uu____18036 =
                                            let uu____18049 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____18049)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____18036
                                           in
                                        FStar_Syntax_Syntax.mk uu____18035
                                         in
                                      uu____18032
                                        FStar_Pervasives_Native.None
                                        head2.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____18030 uu____18031
                                | FStar_Pervasives_Native.None  ->
                                    let uu____18065 =
                                      let uu____18066 = is_return body  in
                                      match uu____18066 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____18070;
                                            FStar_Syntax_Syntax.vars =
                                              uu____18071;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____18076 -> false  in
                                    if uu____18065
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
                                         let uu____18099 =
                                           let uu____18102 =
                                             let uu____18103 =
                                               let uu____18120 =
                                                 let uu____18123 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____18123]  in
                                               (uu____18120, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____18103
                                              in
                                           FStar_Syntax_Syntax.mk uu____18102
                                            in
                                         uu____18099
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____18139 =
                                           let uu____18140 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____18140.FStar_Syntax_Syntax.n
                                            in
                                         match uu____18139 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____18146::uu____18147::[])
                                             ->
                                             let uu____18154 =
                                               let uu____18157 =
                                                 let uu____18158 =
                                                   let uu____18165 =
                                                     let uu____18168 =
                                                       let uu____18169 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____18169
                                                        in
                                                     let uu____18170 =
                                                       let uu____18173 =
                                                         let uu____18174 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____18174
                                                          in
                                                       [uu____18173]  in
                                                     uu____18168 ::
                                                       uu____18170
                                                      in
                                                   (bind1, uu____18165)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____18158
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____18157
                                                in
                                             uu____18154
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____18182 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____18188 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____18188
                                         then
                                           let uu____18191 =
                                             let uu____18192 =
                                               FStar_Syntax_Embeddings.embed_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____18192
                                              in
                                           [uu____18191]
                                         else []  in
                                       let reified =
                                         let uu____18197 =
                                           let uu____18200 =
                                             let uu____18201 =
                                               let uu____18216 =
                                                 let uu____18219 =
                                                   let uu____18222 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____18223 =
                                                     let uu____18226 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____18226]  in
                                                   uu____18222 :: uu____18223
                                                    in
                                                 let uu____18227 =
                                                   let uu____18230 =
                                                     let uu____18233 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____18234 =
                                                       let uu____18237 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head3
                                                          in
                                                       let uu____18238 =
                                                         let uu____18241 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____18242 =
                                                           let uu____18245 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____18245]  in
                                                         uu____18241 ::
                                                           uu____18242
                                                          in
                                                       uu____18237 ::
                                                         uu____18238
                                                        in
                                                     uu____18233 ::
                                                       uu____18234
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____18230
                                                    in
                                                 FStar_List.append
                                                   uu____18219 uu____18227
                                                  in
                                               (bind_inst, uu____18216)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____18201
                                              in
                                           FStar_Syntax_Syntax.mk uu____18200
                                            in
                                         uu____18197
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____18257  ->
                                            let uu____18258 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____18259 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____18258 uu____18259);
                                       (let uu____18260 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____18260 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____18284 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____18284
                        in
                     let uu____18285 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____18285 with
                      | (uu____18286,bind_repr) ->
                          let maybe_unfold_action head3 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____18321 =
                                  let uu____18322 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____18322.FStar_Syntax_Syntax.n  in
                                match uu____18321 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____18328) -> t2
                                | uu____18333 -> head3  in
                              let uu____18334 =
                                let uu____18335 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____18335.FStar_Syntax_Syntax.n  in
                              match uu____18334 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____18341 -> FStar_Pervasives_Native.None
                               in
                            let uu____18342 = maybe_extract_fv head3  in
                            match uu____18342 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____18352 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____18352
                                ->
                                let head4 = norm cfg env [] head3  in
                                let action_unfolded =
                                  let uu____18357 = maybe_extract_fv head4
                                     in
                                  match uu____18357 with
                                  | FStar_Pervasives_Native.Some uu____18362
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____18363 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head4, action_unfolded)
                            | uu____18368 ->
                                (head3, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____18383 =
                              match uu____18383 with
                              | (e,q) ->
                                  let uu____18390 =
                                    let uu____18391 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____18391.FStar_Syntax_Syntax.n  in
                                  (match uu____18390 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       Prims.op_Negation
                                         (FStar_Syntax_Util.is_pure_effect m1)
                                   | uu____18406 -> false)
                               in
                            let uu____18407 =
                              let uu____18408 =
                                let uu____18415 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____18415 :: args  in
                              FStar_Util.for_some is_arg_impure uu____18408
                               in
                            if uu____18407
                            then
                              let uu____18420 =
                                let uu____18421 =
                                  FStar_Syntax_Print.term_to_string head2  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____18421
                                 in
                              failwith uu____18420
                            else ());
                           (let uu____18423 = maybe_unfold_action head_app
                               in
                            match uu____18423 with
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
                                   (fun uu____18464  ->
                                      let uu____18465 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____18466 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____18465 uu____18466);
                                 (let uu____18467 = FStar_List.tl stack  in
                                  norm cfg env uu____18467 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____18469) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____18493 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____18493  in
                     (log cfg
                        (fun uu____18497  ->
                           let uu____18498 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____18498);
                      (let uu____18499 = FStar_List.tl stack  in
                       norm cfg env uu____18499 lifted))
                 | FStar_Syntax_Syntax.Tm_meta (e,uu____18501) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____18626  ->
                               match uu____18626 with
                               | (pat,wopt,tm) ->
                                   let uu____18674 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____18674)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head2.FStar_Syntax_Syntax.pos
                        in
                     let uu____18706 = FStar_List.tl stack  in
                     norm cfg env uu____18706 tm
                 | uu____18707 -> fallback ())

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
              (fun uu____18721  ->
                 let uu____18722 = FStar_Ident.string_of_lid msrc  in
                 let uu____18723 = FStar_Ident.string_of_lid mtgt  in
                 let uu____18724 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____18722
                   uu____18723 uu____18724);
            if FStar_Syntax_Util.is_pure_effect msrc
            then
              (let ed =
                 let uu____18726 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____18726  in
               let uu____18727 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____18727 with
               | (uu____18728,return_repr) ->
                   let return_inst =
                     let uu____18737 =
                       let uu____18738 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____18738.FStar_Syntax_Syntax.n  in
                     match uu____18737 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____18744::[]) ->
                         let uu____18751 =
                           let uu____18754 =
                             let uu____18755 =
                               let uu____18762 =
                                 let uu____18765 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____18765]  in
                               (return_tm, uu____18762)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____18755  in
                           FStar_Syntax_Syntax.mk uu____18754  in
                         uu____18751 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____18773 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____18776 =
                     let uu____18779 =
                       let uu____18780 =
                         let uu____18795 =
                           let uu____18798 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____18799 =
                             let uu____18802 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____18802]  in
                           uu____18798 :: uu____18799  in
                         (return_inst, uu____18795)  in
                       FStar_Syntax_Syntax.Tm_app uu____18780  in
                     FStar_Syntax_Syntax.mk uu____18779  in
                   uu____18776 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos)
            else
              (let uu____18811 =
                 FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
               match uu____18811 with
               | FStar_Pervasives_Native.None  ->
                   let uu____18814 =
                     FStar_Util.format2
                       "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____18814
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____18815;
                     FStar_TypeChecker_Env.mtarget = uu____18816;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____18817;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.None ;_};_}
                   ->
                   let uu____18832 =
                     FStar_Util.format2
                       "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                       (FStar_Ident.text_of_lid msrc)
                       (FStar_Ident.text_of_lid mtgt)
                      in
                   failwith uu____18832
               | FStar_Pervasives_Native.Some
                   { FStar_TypeChecker_Env.msource = uu____18833;
                     FStar_TypeChecker_Env.mtarget = uu____18834;
                     FStar_TypeChecker_Env.mlift =
                       { FStar_TypeChecker_Env.mlift_wp = uu____18835;
                         FStar_TypeChecker_Env.mlift_term =
                           FStar_Pervasives_Native.Some lift;_};_}
                   ->
                   let uu____18859 =
                     env.FStar_TypeChecker_Env.universe_of env t  in
                   let uu____18860 = FStar_Syntax_Util.mk_reify e  in
                   lift uu____18859 t FStar_Syntax_Syntax.tun uu____18860)

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
                (fun uu____18916  ->
                   match uu____18916 with
                   | (a,imp) ->
                       let uu____18927 = norm cfg env [] a  in
                       (uu____18927, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___167_18941 = comp  in
            let uu____18942 =
              let uu____18943 =
                let uu____18952 = norm cfg env [] t  in
                let uu____18953 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____18952, uu____18953)  in
              FStar_Syntax_Syntax.Total uu____18943  in
            {
              FStar_Syntax_Syntax.n = uu____18942;
              FStar_Syntax_Syntax.pos =
                (uu___167_18941.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___167_18941.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___168_18968 = comp  in
            let uu____18969 =
              let uu____18970 =
                let uu____18979 = norm cfg env [] t  in
                let uu____18980 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____18979, uu____18980)  in
              FStar_Syntax_Syntax.GTotal uu____18970  in
            {
              FStar_Syntax_Syntax.n = uu____18969;
              FStar_Syntax_Syntax.pos =
                (uu___168_18968.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___168_18968.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____19032  ->
                      match uu____19032 with
                      | (a,i) ->
                          let uu____19043 = norm cfg env [] a  in
                          (uu____19043, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___88_19054  ->
                      match uu___88_19054 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____19058 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____19058
                      | f -> f))
               in
            let uu___169_19062 = comp  in
            let uu____19063 =
              let uu____19064 =
                let uu___170_19065 = ct  in
                let uu____19066 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____19067 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____19070 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____19066;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___170_19065.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____19067;
                  FStar_Syntax_Syntax.effect_args = uu____19070;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____19064  in
            {
              FStar_Syntax_Syntax.n = uu____19063;
              FStar_Syntax_Syntax.pos =
                (uu___169_19062.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___169_19062.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____19081  ->
        match uu____19081 with
        | (x,imp) ->
            let uu____19084 =
              let uu___171_19085 = x  in
              let uu____19086 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___171_19085.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___171_19085.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____19086
              }  in
            (uu____19084, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____19092 =
          FStar_List.fold_left
            (fun uu____19110  ->
               fun b  ->
                 match uu____19110 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____19092 with | (nbs,uu____19150) -> FStar_List.rev nbs

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
            let uu____19166 =
              let uu___172_19167 = rc  in
              let uu____19168 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___172_19167.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____19168;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___172_19167.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____19166
        | uu____19175 -> lopt

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____19188  ->
               let uu____19189 = FStar_Syntax_Print.tag_of_term t  in
               let uu____19190 = FStar_Syntax_Print.term_to_string t  in
               let uu____19191 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____19198 =
                 let uu____19199 =
                   let uu____19202 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____19202
                    in
                 stack_to_string uu____19199  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____19189 uu____19190 uu____19191 uu____19198);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____19233 =
                     let uu____19234 =
                       let uu____19235 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____19235  in
                     FStar_Util.string_of_int uu____19234  in
                   let uu____19240 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____19241 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____19233 uu____19240 uu____19241)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____19295  ->
                     let uu____19296 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____19296);
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
               let uu____19332 =
                 let uu___173_19333 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___173_19333.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___173_19333.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____19332
           | (Arg (Univ uu____19334,uu____19335,uu____19336))::uu____19337 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____19340,uu____19341))::uu____19342 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____19357,uu____19358),aq,r))::stack1
               when
               let uu____19408 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____19408 ->
               let t2 =
                 let uu____19412 =
                   let uu____19413 =
                     let uu____19414 = closure_as_term cfg env_arg tm  in
                     (uu____19414, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____19413  in
                 uu____19412 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____19420),aq,r))::stack1 ->
               (log cfg
                  (fun uu____19473  ->
                     let uu____19474 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____19474);
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
                  (let uu____19484 = FStar_ST.op_Bang m  in
                   match uu____19484 with
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
                   | FStar_Pervasives_Native.Some (uu____19621,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____19668 =
                 log cfg
                   (fun uu____19672  ->
                      let uu____19673 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____19673);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____19677 =
                 let uu____19678 = FStar_Syntax_Subst.compress t1  in
                 uu____19678.FStar_Syntax_Syntax.n  in
               (match uu____19677 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____19705 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____19705  in
                    (log cfg
                       (fun uu____19709  ->
                          let uu____19710 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____19710);
                     (let uu____19711 = FStar_List.tl stack  in
                      norm cfg env1 uu____19711 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____19712);
                       FStar_Syntax_Syntax.pos = uu____19713;
                       FStar_Syntax_Syntax.vars = uu____19714;_},(e,uu____19716)::[])
                    -> norm cfg env1 stack' e
                | uu____19745 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____19765  ->
                     let uu____19766 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____19766);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____19771 =
                   log cfg
                     (fun uu____19776  ->
                        let uu____19777 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____19778 =
                          let uu____19779 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____19796  ->
                                    match uu____19796 with
                                    | (p,uu____19806,uu____19807) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____19779
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____19777 uu____19778);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___89_19824  ->
                                match uu___89_19824 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____19825 -> false))
                         in
                      let uu___174_19826 = cfg  in
                      {
                        steps =
                          (let uu___175_19829 = cfg.steps  in
                           {
                             beta = (uu___175_19829.beta);
                             iota = (uu___175_19829.iota);
                             zeta = false;
                             weak = (uu___175_19829.weak);
                             hnf = (uu___175_19829.hnf);
                             primops = (uu___175_19829.primops);
                             no_delta_steps = (uu___175_19829.no_delta_steps);
                             unfold_until = (uu___175_19829.unfold_until);
                             unfold_only = (uu___175_19829.unfold_only);
                             unfold_attr = (uu___175_19829.unfold_attr);
                             unfold_tac = (uu___175_19829.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___175_19829.pure_subterms_within_computations);
                             simplify = (uu___175_19829.simplify);
                             erase_universes =
                               (uu___175_19829.erase_universes);
                             allow_unbound_universes =
                               (uu___175_19829.allow_unbound_universes);
                             reify_ = (uu___175_19829.reify_);
                             compress_uvars = (uu___175_19829.compress_uvars);
                             no_full_norm = (uu___175_19829.no_full_norm);
                             check_no_uvars = (uu___175_19829.check_no_uvars);
                             unmeta = (uu___175_19829.unmeta);
                             unascribe = (uu___175_19829.unascribe)
                           });
                        tcenv = (uu___174_19826.tcenv);
                        debug = (uu___174_19826.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___174_19826.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___174_19826.memoize_lazy);
                        normalize_pure_lets =
                          (uu___174_19826.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____19861 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____19882 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____19942  ->
                                    fun uu____19943  ->
                                      match (uu____19942, uu____19943) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____20034 = norm_pat env3 p1
                                             in
                                          (match uu____20034 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____19882 with
                           | (pats1,env3) ->
                               ((let uu___176_20116 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___176_20116.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___177_20135 = x  in
                            let uu____20136 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___177_20135.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___177_20135.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20136
                            }  in
                          ((let uu___178_20150 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___178_20150.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___179_20161 = x  in
                            let uu____20162 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___179_20161.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___179_20161.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20162
                            }  in
                          ((let uu___180_20176 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___180_20176.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___181_20192 = x  in
                            let uu____20193 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___181_20192.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___181_20192.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20193
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___182_20200 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___182_20200.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____20210 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____20224 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____20224 with
                                  | (p,wopt,e) ->
                                      let uu____20244 = norm_pat env1 p  in
                                      (match uu____20244 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____20269 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____20269
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____20275 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____20275)
                    in
                 let rec is_cons head1 =
                   let uu____20280 =
                     let uu____20281 = FStar_Syntax_Subst.compress head1  in
                     uu____20281.FStar_Syntax_Syntax.n  in
                   match uu____20280 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____20285) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____20290 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20291;
                         FStar_Syntax_Syntax.fv_delta = uu____20292;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20293;
                         FStar_Syntax_Syntax.fv_delta = uu____20294;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____20295);_}
                       -> true
                   | uu____20302 -> false  in
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
                   let uu____20447 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____20447 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____20534 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____20573 ->
                                 let uu____20574 =
                                   let uu____20575 = is_cons head1  in
                                   Prims.op_Negation uu____20575  in
                                 FStar_Util.Inr uu____20574)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____20600 =
                              let uu____20601 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____20601.FStar_Syntax_Syntax.n  in
                            (match uu____20600 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____20619 ->
                                 let uu____20620 =
                                   let uu____20621 = is_cons head1  in
                                   Prims.op_Negation uu____20621  in
                                 FStar_Util.Inr uu____20620))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____20690)::rest_a,(p1,uu____20693)::rest_p) ->
                       let uu____20737 = matches_pat t2 p1  in
                       (match uu____20737 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____20786 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____20892 = matches_pat scrutinee1 p1  in
                       (match uu____20892 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____20932  ->
                                  let uu____20933 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____20934 =
                                    let uu____20935 =
                                      FStar_List.map
                                        (fun uu____20945  ->
                                           match uu____20945 with
                                           | (uu____20950,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____20935
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____20933 uu____20934);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____20981  ->
                                       match uu____20981 with
                                       | (bv,t2) ->
                                           let uu____21004 =
                                             let uu____21011 =
                                               let uu____21014 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____21014
                                                in
                                             let uu____21015 =
                                               let uu____21016 =
                                                 let uu____21047 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____21047, false)
                                                  in
                                               Clos uu____21016  in
                                             (uu____21011, uu____21015)  in
                                           uu____21004 :: env2) env1 s
                                 in
                              let uu____21164 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____21164)))
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
               (fun uu___90_21192  ->
                  match uu___90_21192 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____21196 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____21202 -> d  in
        let uu____21205 = to_fsteps s  in
        let uu____21206 =
          let uu____21207 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____21208 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____21209 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____21210 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____21211 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____21207;
            primop = uu____21208;
            b380 = uu____21209;
            norm_delayed = uu____21210;
            print_normalized = uu____21211
          }  in
        let uu____21212 = add_steps built_in_primitive_steps psteps  in
        let uu____21215 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____21217 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____21217)
           in
        {
          steps = uu____21205;
          tcenv = e;
          debug = uu____21206;
          delta_level = d1;
          primitive_steps = uu____21212;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____21215
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
      fun t  -> let uu____21275 = config s e  in norm_comp uu____21275 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____21288 = config [] env  in norm_universe uu____21288 [] u
  
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
        let uu____21306 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21306  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____21313 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___183_21332 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___183_21332.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___183_21332.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____21339 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____21339
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
                  let uu___184_21348 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___184_21348.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___184_21348.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___184_21348.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___185_21350 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___185_21350.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___185_21350.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___185_21350.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___185_21350.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___186_21351 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___186_21351.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___186_21351.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____21353 -> c
  
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
        let uu____21365 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21365  in
      let uu____21372 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____21372
      then
        match downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name
        with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____21376  ->
                 let uu____21377 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____21377)
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
            ((let uu____21394 =
                let uu____21399 =
                  let uu____21400 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____21400
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____21399)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____21394);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____21411 = config [AllowUnboundUniverses] env  in
          norm_comp uu____21411 [] c
        with
        | e ->
            ((let uu____21424 =
                let uu____21429 =
                  let uu____21430 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____21430
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____21429)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____21424);
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
                   let uu____21467 =
                     let uu____21468 =
                       let uu____21475 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____21475)  in
                     FStar_Syntax_Syntax.Tm_refine uu____21468  in
                   mk uu____21467 t01.FStar_Syntax_Syntax.pos
               | uu____21480 -> t2)
          | uu____21481 -> t2  in
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
        let uu____21521 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____21521 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____21550 ->
                 let uu____21557 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____21557 with
                  | (actuals,uu____21567,uu____21568) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____21582 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____21582 with
                         | (binders,args) ->
                             let uu____21599 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____21599
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
      | uu____21607 ->
          let uu____21608 = FStar_Syntax_Util.head_and_args t  in
          (match uu____21608 with
           | (head1,args) ->
               let uu____21645 =
                 let uu____21646 = FStar_Syntax_Subst.compress head1  in
                 uu____21646.FStar_Syntax_Syntax.n  in
               (match uu____21645 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____21649,thead) ->
                    let uu____21675 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____21675 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____21717 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___191_21725 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___191_21725.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___191_21725.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___191_21725.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___191_21725.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___191_21725.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___191_21725.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___191_21725.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___191_21725.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___191_21725.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___191_21725.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___191_21725.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___191_21725.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___191_21725.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___191_21725.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___191_21725.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___191_21725.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___191_21725.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___191_21725.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___191_21725.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___191_21725.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___191_21725.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___191_21725.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___191_21725.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___191_21725.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___191_21725.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___191_21725.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___191_21725.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___191_21725.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___191_21725.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___191_21725.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___191_21725.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___191_21725.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____21717 with
                            | (uu____21726,ty,uu____21728) ->
                                eta_expand_with_type env t ty))
                | uu____21729 ->
                    let uu____21730 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___192_21738 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___192_21738.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___192_21738.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___192_21738.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___192_21738.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___192_21738.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___192_21738.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___192_21738.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___192_21738.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___192_21738.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___192_21738.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___192_21738.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___192_21738.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___192_21738.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___192_21738.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___192_21738.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___192_21738.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___192_21738.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___192_21738.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___192_21738.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___192_21738.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___192_21738.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___192_21738.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___192_21738.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___192_21738.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___192_21738.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___192_21738.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth =
                             (uu___192_21738.FStar_TypeChecker_Env.synth);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___192_21738.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___192_21738.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___192_21738.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___192_21738.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___192_21738.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____21730 with
                     | (uu____21739,ty,uu____21741) ->
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
      let uu___193_21798 = x  in
      let uu____21799 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___193_21798.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___193_21798.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____21799
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____21802 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____21827 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____21828 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____21829 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____21830 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____21837 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____21838 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____21839 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___194_21867 = rc  in
          let uu____21868 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____21875 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___194_21867.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____21868;
            FStar_Syntax_Syntax.residual_flags = uu____21875
          }  in
        let uu____21878 =
          let uu____21879 =
            let uu____21896 = elim_delayed_subst_binders bs  in
            let uu____21903 = elim_delayed_subst_term t2  in
            let uu____21904 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____21896, uu____21903, uu____21904)  in
          FStar_Syntax_Syntax.Tm_abs uu____21879  in
        mk1 uu____21878
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____21933 =
          let uu____21934 =
            let uu____21947 = elim_delayed_subst_binders bs  in
            let uu____21954 = elim_delayed_subst_comp c  in
            (uu____21947, uu____21954)  in
          FStar_Syntax_Syntax.Tm_arrow uu____21934  in
        mk1 uu____21933
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____21967 =
          let uu____21968 =
            let uu____21975 = elim_bv bv  in
            let uu____21976 = elim_delayed_subst_term phi  in
            (uu____21975, uu____21976)  in
          FStar_Syntax_Syntax.Tm_refine uu____21968  in
        mk1 uu____21967
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____21999 =
          let uu____22000 =
            let uu____22015 = elim_delayed_subst_term t2  in
            let uu____22016 = elim_delayed_subst_args args  in
            (uu____22015, uu____22016)  in
          FStar_Syntax_Syntax.Tm_app uu____22000  in
        mk1 uu____21999
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___195_22080 = p  in
              let uu____22081 =
                let uu____22082 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____22082  in
              {
                FStar_Syntax_Syntax.v = uu____22081;
                FStar_Syntax_Syntax.p =
                  (uu___195_22080.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___196_22084 = p  in
              let uu____22085 =
                let uu____22086 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____22086  in
              {
                FStar_Syntax_Syntax.v = uu____22085;
                FStar_Syntax_Syntax.p =
                  (uu___196_22084.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___197_22093 = p  in
              let uu____22094 =
                let uu____22095 =
                  let uu____22102 = elim_bv x  in
                  let uu____22103 = elim_delayed_subst_term t0  in
                  (uu____22102, uu____22103)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____22095  in
              {
                FStar_Syntax_Syntax.v = uu____22094;
                FStar_Syntax_Syntax.p =
                  (uu___197_22093.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___198_22122 = p  in
              let uu____22123 =
                let uu____22124 =
                  let uu____22137 =
                    FStar_List.map
                      (fun uu____22160  ->
                         match uu____22160 with
                         | (x,b) ->
                             let uu____22173 = elim_pat x  in
                             (uu____22173, b)) pats
                     in
                  (fv, uu____22137)  in
                FStar_Syntax_Syntax.Pat_cons uu____22124  in
              {
                FStar_Syntax_Syntax.v = uu____22123;
                FStar_Syntax_Syntax.p =
                  (uu___198_22122.FStar_Syntax_Syntax.p)
              }
          | uu____22186 -> p  in
        let elim_branch uu____22208 =
          match uu____22208 with
          | (pat,wopt,t3) ->
              let uu____22234 = elim_pat pat  in
              let uu____22237 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____22240 = elim_delayed_subst_term t3  in
              (uu____22234, uu____22237, uu____22240)
           in
        let uu____22245 =
          let uu____22246 =
            let uu____22269 = elim_delayed_subst_term t2  in
            let uu____22270 = FStar_List.map elim_branch branches  in
            (uu____22269, uu____22270)  in
          FStar_Syntax_Syntax.Tm_match uu____22246  in
        mk1 uu____22245
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____22379 =
          match uu____22379 with
          | (tc,topt) ->
              let uu____22414 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____22424 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____22424
                | FStar_Util.Inr c ->
                    let uu____22426 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____22426
                 in
              let uu____22427 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____22414, uu____22427)
           in
        let uu____22436 =
          let uu____22437 =
            let uu____22464 = elim_delayed_subst_term t2  in
            let uu____22465 = elim_ascription a  in
            (uu____22464, uu____22465, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____22437  in
        mk1 uu____22436
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___199_22510 = lb  in
          let uu____22511 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____22514 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___199_22510.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___199_22510.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____22511;
            FStar_Syntax_Syntax.lbeff =
              (uu___199_22510.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____22514;
            FStar_Syntax_Syntax.lbattrs =
              (uu___199_22510.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___199_22510.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____22517 =
          let uu____22518 =
            let uu____22531 =
              let uu____22538 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____22538)  in
            let uu____22547 = elim_delayed_subst_term t2  in
            (uu____22531, uu____22547)  in
          FStar_Syntax_Syntax.Tm_let uu____22518  in
        mk1 uu____22517
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____22580 =
          let uu____22581 =
            let uu____22598 = elim_delayed_subst_term t2  in
            (uv, uu____22598)  in
          FStar_Syntax_Syntax.Tm_uvar uu____22581  in
        mk1 uu____22580
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____22615 =
          let uu____22616 =
            let uu____22623 = elim_delayed_subst_term t2  in
            let uu____22624 = elim_delayed_subst_meta md  in
            (uu____22623, uu____22624)  in
          FStar_Syntax_Syntax.Tm_meta uu____22616  in
        mk1 uu____22615

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___91_22631  ->
         match uu___91_22631 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____22635 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____22635
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
        let uu____22656 =
          let uu____22657 =
            let uu____22666 = elim_delayed_subst_term t  in
            (uu____22666, uopt)  in
          FStar_Syntax_Syntax.Total uu____22657  in
        mk1 uu____22656
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____22679 =
          let uu____22680 =
            let uu____22689 = elim_delayed_subst_term t  in
            (uu____22689, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____22680  in
        mk1 uu____22679
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___200_22694 = ct  in
          let uu____22695 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____22698 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____22707 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___200_22694.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___200_22694.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____22695;
            FStar_Syntax_Syntax.effect_args = uu____22698;
            FStar_Syntax_Syntax.flags = uu____22707
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___92_22710  ->
    match uu___92_22710 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____22722 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____22722
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____22755 =
          let uu____22762 = elim_delayed_subst_term t  in (m, uu____22762)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____22755
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____22770 =
          let uu____22779 = elim_delayed_subst_term t  in
          (m1, m2, uu____22779)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____22770
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____22802  ->
         match uu____22802 with
         | (t,q) ->
             let uu____22813 = elim_delayed_subst_term t  in (uu____22813, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____22833  ->
         match uu____22833 with
         | (x,q) ->
             let uu____22844 =
               let uu___201_22845 = x  in
               let uu____22846 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___201_22845.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___201_22845.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____22846
               }  in
             (uu____22844, q)) bs

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
            | (uu____22922,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____22928,FStar_Util.Inl t) ->
                let uu____22934 =
                  let uu____22937 =
                    let uu____22938 =
                      let uu____22951 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____22951)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____22938  in
                  FStar_Syntax_Syntax.mk uu____22937  in
                uu____22934 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____22955 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____22955 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____22983 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____23038 ->
                    let uu____23039 =
                      let uu____23048 =
                        let uu____23049 = FStar_Syntax_Subst.compress t4  in
                        uu____23049.FStar_Syntax_Syntax.n  in
                      (uu____23048, tc)  in
                    (match uu____23039 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____23074) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____23111) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____23150,FStar_Util.Inl uu____23151) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____23174 -> failwith "Impossible")
                 in
              (match uu____22983 with
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
          let uu____23279 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____23279 with
          | (univ_names1,binders1,tc) ->
              let uu____23337 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____23337)
  
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
          let uu____23372 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____23372 with
          | (univ_names1,binders1,tc) ->
              let uu____23432 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____23432)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____23465 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____23465 with
           | (univ_names1,binders1,typ1) ->
               let uu___202_23493 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___202_23493.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___202_23493.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___202_23493.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___202_23493.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___203_23514 = s  in
          let uu____23515 =
            let uu____23516 =
              let uu____23525 = FStar_List.map (elim_uvars env) sigs  in
              (uu____23525, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____23516  in
          {
            FStar_Syntax_Syntax.sigel = uu____23515;
            FStar_Syntax_Syntax.sigrng =
              (uu___203_23514.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___203_23514.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___203_23514.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___203_23514.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____23542 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____23542 with
           | (univ_names1,uu____23560,typ1) ->
               let uu___204_23574 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___204_23574.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___204_23574.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___204_23574.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___204_23574.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____23580 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____23580 with
           | (univ_names1,uu____23598,typ1) ->
               let uu___205_23612 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___205_23612.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___205_23612.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___205_23612.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___205_23612.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____23646 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____23646 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____23669 =
                            let uu____23670 =
                              let uu____23671 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____23671  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____23670
                             in
                          elim_delayed_subst_term uu____23669  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___206_23674 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___206_23674.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___206_23674.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___206_23674.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___206_23674.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___207_23675 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___207_23675.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___207_23675.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___207_23675.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___207_23675.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___208_23687 = s  in
          let uu____23688 =
            let uu____23689 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____23689  in
          {
            FStar_Syntax_Syntax.sigel = uu____23688;
            FStar_Syntax_Syntax.sigrng =
              (uu___208_23687.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___208_23687.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___208_23687.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___208_23687.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____23693 = elim_uvars_aux_t env us [] t  in
          (match uu____23693 with
           | (us1,uu____23711,t1) ->
               let uu___209_23725 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___209_23725.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___209_23725.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___209_23725.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___209_23725.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____23726 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____23728 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____23728 with
           | (univs1,binders,signature) ->
               let uu____23756 =
                 let uu____23765 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____23765 with
                 | (univs_opening,univs2) ->
                     let uu____23792 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____23792)
                  in
               (match uu____23756 with
                | (univs_opening,univs_closing) ->
                    let uu____23809 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____23815 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____23816 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____23815, uu____23816)  in
                    (match uu____23809 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____23838 =
                           match uu____23838 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____23856 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____23856 with
                                | (us1,t1) ->
                                    let uu____23867 =
                                      let uu____23872 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____23879 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____23872, uu____23879)  in
                                    (match uu____23867 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____23892 =
                                           let uu____23897 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____23906 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____23897, uu____23906)  in
                                         (match uu____23892 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____23922 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____23922
                                                 in
                                              let uu____23923 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____23923 with
                                               | (uu____23944,uu____23945,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____23960 =
                                                       let uu____23961 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____23961
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____23960
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____23966 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____23966 with
                           | (uu____23979,uu____23980,t1) -> t1  in
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
                             | uu____24040 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____24057 =
                               let uu____24058 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____24058.FStar_Syntax_Syntax.n  in
                             match uu____24057 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____24117 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____24146 =
                               let uu____24147 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____24147.FStar_Syntax_Syntax.n  in
                             match uu____24146 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____24168) ->
                                 let uu____24189 = destruct_action_body body
                                    in
                                 (match uu____24189 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____24234 ->
                                 let uu____24235 = destruct_action_body t  in
                                 (match uu____24235 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____24284 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____24284 with
                           | (action_univs,t) ->
                               let uu____24293 = destruct_action_typ_templ t
                                  in
                               (match uu____24293 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___210_24334 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___210_24334.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___210_24334.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___211_24336 = ed  in
                           let uu____24337 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____24338 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____24339 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____24340 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____24341 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____24342 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____24343 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____24344 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____24345 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____24346 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____24347 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____24348 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____24349 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____24350 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___211_24336.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___211_24336.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____24337;
                             FStar_Syntax_Syntax.bind_wp = uu____24338;
                             FStar_Syntax_Syntax.if_then_else = uu____24339;
                             FStar_Syntax_Syntax.ite_wp = uu____24340;
                             FStar_Syntax_Syntax.stronger = uu____24341;
                             FStar_Syntax_Syntax.close_wp = uu____24342;
                             FStar_Syntax_Syntax.assert_p = uu____24343;
                             FStar_Syntax_Syntax.assume_p = uu____24344;
                             FStar_Syntax_Syntax.null_wp = uu____24345;
                             FStar_Syntax_Syntax.trivial = uu____24346;
                             FStar_Syntax_Syntax.repr = uu____24347;
                             FStar_Syntax_Syntax.return_repr = uu____24348;
                             FStar_Syntax_Syntax.bind_repr = uu____24349;
                             FStar_Syntax_Syntax.actions = uu____24350;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___211_24336.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___212_24353 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___212_24353.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___212_24353.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___212_24353.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___212_24353.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___93_24370 =
            match uu___93_24370 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____24397 = elim_uvars_aux_t env us [] t  in
                (match uu____24397 with
                 | (us1,uu____24421,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___213_24440 = sub_eff  in
            let uu____24441 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____24444 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___213_24440.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___213_24440.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____24441;
              FStar_Syntax_Syntax.lift = uu____24444
            }  in
          let uu___214_24447 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___214_24447.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___214_24447.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___214_24447.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___214_24447.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____24457 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____24457 with
           | (univ_names1,binders1,comp1) ->
               let uu___215_24491 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___215_24491.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___215_24491.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___215_24491.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___215_24491.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____24502 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  