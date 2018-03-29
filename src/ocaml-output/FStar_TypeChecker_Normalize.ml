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
      fun uu___77_180  ->
        match uu___77_180 with
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
      let add_opt x uu___78_1038 =
        match uu___78_1038 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___96_1058 = fs  in
          {
            beta = true;
            iota = (uu___96_1058.iota);
            zeta = (uu___96_1058.zeta);
            weak = (uu___96_1058.weak);
            hnf = (uu___96_1058.hnf);
            primops = (uu___96_1058.primops);
            no_delta_steps = (uu___96_1058.no_delta_steps);
            unfold_until = (uu___96_1058.unfold_until);
            unfold_only = (uu___96_1058.unfold_only);
            unfold_attr = (uu___96_1058.unfold_attr);
            unfold_tac = (uu___96_1058.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1058.pure_subterms_within_computations);
            simplify = (uu___96_1058.simplify);
            erase_universes = (uu___96_1058.erase_universes);
            allow_unbound_universes = (uu___96_1058.allow_unbound_universes);
            reify_ = (uu___96_1058.reify_);
            compress_uvars = (uu___96_1058.compress_uvars);
            no_full_norm = (uu___96_1058.no_full_norm);
            check_no_uvars = (uu___96_1058.check_no_uvars);
            unmeta = (uu___96_1058.unmeta);
            unascribe = (uu___96_1058.unascribe)
          }
      | Iota  ->
          let uu___97_1059 = fs  in
          {
            beta = (uu___97_1059.beta);
            iota = true;
            zeta = (uu___97_1059.zeta);
            weak = (uu___97_1059.weak);
            hnf = (uu___97_1059.hnf);
            primops = (uu___97_1059.primops);
            no_delta_steps = (uu___97_1059.no_delta_steps);
            unfold_until = (uu___97_1059.unfold_until);
            unfold_only = (uu___97_1059.unfold_only);
            unfold_attr = (uu___97_1059.unfold_attr);
            unfold_tac = (uu___97_1059.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1059.pure_subterms_within_computations);
            simplify = (uu___97_1059.simplify);
            erase_universes = (uu___97_1059.erase_universes);
            allow_unbound_universes = (uu___97_1059.allow_unbound_universes);
            reify_ = (uu___97_1059.reify_);
            compress_uvars = (uu___97_1059.compress_uvars);
            no_full_norm = (uu___97_1059.no_full_norm);
            check_no_uvars = (uu___97_1059.check_no_uvars);
            unmeta = (uu___97_1059.unmeta);
            unascribe = (uu___97_1059.unascribe)
          }
      | Zeta  ->
          let uu___98_1060 = fs  in
          {
            beta = (uu___98_1060.beta);
            iota = (uu___98_1060.iota);
            zeta = true;
            weak = (uu___98_1060.weak);
            hnf = (uu___98_1060.hnf);
            primops = (uu___98_1060.primops);
            no_delta_steps = (uu___98_1060.no_delta_steps);
            unfold_until = (uu___98_1060.unfold_until);
            unfold_only = (uu___98_1060.unfold_only);
            unfold_attr = (uu___98_1060.unfold_attr);
            unfold_tac = (uu___98_1060.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1060.pure_subterms_within_computations);
            simplify = (uu___98_1060.simplify);
            erase_universes = (uu___98_1060.erase_universes);
            allow_unbound_universes = (uu___98_1060.allow_unbound_universes);
            reify_ = (uu___98_1060.reify_);
            compress_uvars = (uu___98_1060.compress_uvars);
            no_full_norm = (uu___98_1060.no_full_norm);
            check_no_uvars = (uu___98_1060.check_no_uvars);
            unmeta = (uu___98_1060.unmeta);
            unascribe = (uu___98_1060.unascribe)
          }
      | Exclude (Beta ) ->
          let uu___99_1061 = fs  in
          {
            beta = false;
            iota = (uu___99_1061.iota);
            zeta = (uu___99_1061.zeta);
            weak = (uu___99_1061.weak);
            hnf = (uu___99_1061.hnf);
            primops = (uu___99_1061.primops);
            no_delta_steps = (uu___99_1061.no_delta_steps);
            unfold_until = (uu___99_1061.unfold_until);
            unfold_only = (uu___99_1061.unfold_only);
            unfold_attr = (uu___99_1061.unfold_attr);
            unfold_tac = (uu___99_1061.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1061.pure_subterms_within_computations);
            simplify = (uu___99_1061.simplify);
            erase_universes = (uu___99_1061.erase_universes);
            allow_unbound_universes = (uu___99_1061.allow_unbound_universes);
            reify_ = (uu___99_1061.reify_);
            compress_uvars = (uu___99_1061.compress_uvars);
            no_full_norm = (uu___99_1061.no_full_norm);
            check_no_uvars = (uu___99_1061.check_no_uvars);
            unmeta = (uu___99_1061.unmeta);
            unascribe = (uu___99_1061.unascribe)
          }
      | Exclude (Iota ) ->
          let uu___100_1062 = fs  in
          {
            beta = (uu___100_1062.beta);
            iota = false;
            zeta = (uu___100_1062.zeta);
            weak = (uu___100_1062.weak);
            hnf = (uu___100_1062.hnf);
            primops = (uu___100_1062.primops);
            no_delta_steps = (uu___100_1062.no_delta_steps);
            unfold_until = (uu___100_1062.unfold_until);
            unfold_only = (uu___100_1062.unfold_only);
            unfold_attr = (uu___100_1062.unfold_attr);
            unfold_tac = (uu___100_1062.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1062.pure_subterms_within_computations);
            simplify = (uu___100_1062.simplify);
            erase_universes = (uu___100_1062.erase_universes);
            allow_unbound_universes = (uu___100_1062.allow_unbound_universes);
            reify_ = (uu___100_1062.reify_);
            compress_uvars = (uu___100_1062.compress_uvars);
            no_full_norm = (uu___100_1062.no_full_norm);
            check_no_uvars = (uu___100_1062.check_no_uvars);
            unmeta = (uu___100_1062.unmeta);
            unascribe = (uu___100_1062.unascribe)
          }
      | Exclude (Zeta ) ->
          let uu___101_1063 = fs  in
          {
            beta = (uu___101_1063.beta);
            iota = (uu___101_1063.iota);
            zeta = false;
            weak = (uu___101_1063.weak);
            hnf = (uu___101_1063.hnf);
            primops = (uu___101_1063.primops);
            no_delta_steps = (uu___101_1063.no_delta_steps);
            unfold_until = (uu___101_1063.unfold_until);
            unfold_only = (uu___101_1063.unfold_only);
            unfold_attr = (uu___101_1063.unfold_attr);
            unfold_tac = (uu___101_1063.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1063.pure_subterms_within_computations);
            simplify = (uu___101_1063.simplify);
            erase_universes = (uu___101_1063.erase_universes);
            allow_unbound_universes = (uu___101_1063.allow_unbound_universes);
            reify_ = (uu___101_1063.reify_);
            compress_uvars = (uu___101_1063.compress_uvars);
            no_full_norm = (uu___101_1063.no_full_norm);
            check_no_uvars = (uu___101_1063.check_no_uvars);
            unmeta = (uu___101_1063.unmeta);
            unascribe = (uu___101_1063.unascribe)
          }
      | Exclude uu____1064 -> failwith "Bad exclude"
      | Weak  ->
          let uu___102_1065 = fs  in
          {
            beta = (uu___102_1065.beta);
            iota = (uu___102_1065.iota);
            zeta = (uu___102_1065.zeta);
            weak = true;
            hnf = (uu___102_1065.hnf);
            primops = (uu___102_1065.primops);
            no_delta_steps = (uu___102_1065.no_delta_steps);
            unfold_until = (uu___102_1065.unfold_until);
            unfold_only = (uu___102_1065.unfold_only);
            unfold_attr = (uu___102_1065.unfold_attr);
            unfold_tac = (uu___102_1065.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1065.pure_subterms_within_computations);
            simplify = (uu___102_1065.simplify);
            erase_universes = (uu___102_1065.erase_universes);
            allow_unbound_universes = (uu___102_1065.allow_unbound_universes);
            reify_ = (uu___102_1065.reify_);
            compress_uvars = (uu___102_1065.compress_uvars);
            no_full_norm = (uu___102_1065.no_full_norm);
            check_no_uvars = (uu___102_1065.check_no_uvars);
            unmeta = (uu___102_1065.unmeta);
            unascribe = (uu___102_1065.unascribe)
          }
      | HNF  ->
          let uu___103_1066 = fs  in
          {
            beta = (uu___103_1066.beta);
            iota = (uu___103_1066.iota);
            zeta = (uu___103_1066.zeta);
            weak = (uu___103_1066.weak);
            hnf = true;
            primops = (uu___103_1066.primops);
            no_delta_steps = (uu___103_1066.no_delta_steps);
            unfold_until = (uu___103_1066.unfold_until);
            unfold_only = (uu___103_1066.unfold_only);
            unfold_attr = (uu___103_1066.unfold_attr);
            unfold_tac = (uu___103_1066.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1066.pure_subterms_within_computations);
            simplify = (uu___103_1066.simplify);
            erase_universes = (uu___103_1066.erase_universes);
            allow_unbound_universes = (uu___103_1066.allow_unbound_universes);
            reify_ = (uu___103_1066.reify_);
            compress_uvars = (uu___103_1066.compress_uvars);
            no_full_norm = (uu___103_1066.no_full_norm);
            check_no_uvars = (uu___103_1066.check_no_uvars);
            unmeta = (uu___103_1066.unmeta);
            unascribe = (uu___103_1066.unascribe)
          }
      | Primops  ->
          let uu___104_1067 = fs  in
          {
            beta = (uu___104_1067.beta);
            iota = (uu___104_1067.iota);
            zeta = (uu___104_1067.zeta);
            weak = (uu___104_1067.weak);
            hnf = (uu___104_1067.hnf);
            primops = true;
            no_delta_steps = (uu___104_1067.no_delta_steps);
            unfold_until = (uu___104_1067.unfold_until);
            unfold_only = (uu___104_1067.unfold_only);
            unfold_attr = (uu___104_1067.unfold_attr);
            unfold_tac = (uu___104_1067.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1067.pure_subterms_within_computations);
            simplify = (uu___104_1067.simplify);
            erase_universes = (uu___104_1067.erase_universes);
            allow_unbound_universes = (uu___104_1067.allow_unbound_universes);
            reify_ = (uu___104_1067.reify_);
            compress_uvars = (uu___104_1067.compress_uvars);
            no_full_norm = (uu___104_1067.no_full_norm);
            check_no_uvars = (uu___104_1067.check_no_uvars);
            unmeta = (uu___104_1067.unmeta);
            unascribe = (uu___104_1067.unascribe)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | NoDeltaSteps  ->
          let uu___105_1068 = fs  in
          {
            beta = (uu___105_1068.beta);
            iota = (uu___105_1068.iota);
            zeta = (uu___105_1068.zeta);
            weak = (uu___105_1068.weak);
            hnf = (uu___105_1068.hnf);
            primops = (uu___105_1068.primops);
            no_delta_steps = true;
            unfold_until = (uu___105_1068.unfold_until);
            unfold_only = (uu___105_1068.unfold_only);
            unfold_attr = (uu___105_1068.unfold_attr);
            unfold_tac = (uu___105_1068.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1068.pure_subterms_within_computations);
            simplify = (uu___105_1068.simplify);
            erase_universes = (uu___105_1068.erase_universes);
            allow_unbound_universes = (uu___105_1068.allow_unbound_universes);
            reify_ = (uu___105_1068.reify_);
            compress_uvars = (uu___105_1068.compress_uvars);
            no_full_norm = (uu___105_1068.no_full_norm);
            check_no_uvars = (uu___105_1068.check_no_uvars);
            unmeta = (uu___105_1068.unmeta);
            unascribe = (uu___105_1068.unascribe)
          }
      | UnfoldUntil d ->
          let uu___106_1070 = fs  in
          {
            beta = (uu___106_1070.beta);
            iota = (uu___106_1070.iota);
            zeta = (uu___106_1070.zeta);
            weak = (uu___106_1070.weak);
            hnf = (uu___106_1070.hnf);
            primops = (uu___106_1070.primops);
            no_delta_steps = (uu___106_1070.no_delta_steps);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___106_1070.unfold_only);
            unfold_attr = (uu___106_1070.unfold_attr);
            unfold_tac = (uu___106_1070.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1070.pure_subterms_within_computations);
            simplify = (uu___106_1070.simplify);
            erase_universes = (uu___106_1070.erase_universes);
            allow_unbound_universes = (uu___106_1070.allow_unbound_universes);
            reify_ = (uu___106_1070.reify_);
            compress_uvars = (uu___106_1070.compress_uvars);
            no_full_norm = (uu___106_1070.no_full_norm);
            check_no_uvars = (uu___106_1070.check_no_uvars);
            unmeta = (uu___106_1070.unmeta);
            unascribe = (uu___106_1070.unascribe)
          }
      | UnfoldOnly lids ->
          let uu___107_1074 = fs  in
          {
            beta = (uu___107_1074.beta);
            iota = (uu___107_1074.iota);
            zeta = (uu___107_1074.zeta);
            weak = (uu___107_1074.weak);
            hnf = (uu___107_1074.hnf);
            primops = (uu___107_1074.primops);
            no_delta_steps = (uu___107_1074.no_delta_steps);
            unfold_until = (uu___107_1074.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___107_1074.unfold_attr);
            unfold_tac = (uu___107_1074.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1074.pure_subterms_within_computations);
            simplify = (uu___107_1074.simplify);
            erase_universes = (uu___107_1074.erase_universes);
            allow_unbound_universes = (uu___107_1074.allow_unbound_universes);
            reify_ = (uu___107_1074.reify_);
            compress_uvars = (uu___107_1074.compress_uvars);
            no_full_norm = (uu___107_1074.no_full_norm);
            check_no_uvars = (uu___107_1074.check_no_uvars);
            unmeta = (uu___107_1074.unmeta);
            unascribe = (uu___107_1074.unascribe)
          }
      | UnfoldAttr attr ->
          let uu___108_1078 = fs  in
          {
            beta = (uu___108_1078.beta);
            iota = (uu___108_1078.iota);
            zeta = (uu___108_1078.zeta);
            weak = (uu___108_1078.weak);
            hnf = (uu___108_1078.hnf);
            primops = (uu___108_1078.primops);
            no_delta_steps = (uu___108_1078.no_delta_steps);
            unfold_until = (uu___108_1078.unfold_until);
            unfold_only = (uu___108_1078.unfold_only);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___108_1078.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1078.pure_subterms_within_computations);
            simplify = (uu___108_1078.simplify);
            erase_universes = (uu___108_1078.erase_universes);
            allow_unbound_universes = (uu___108_1078.allow_unbound_universes);
            reify_ = (uu___108_1078.reify_);
            compress_uvars = (uu___108_1078.compress_uvars);
            no_full_norm = (uu___108_1078.no_full_norm);
            check_no_uvars = (uu___108_1078.check_no_uvars);
            unmeta = (uu___108_1078.unmeta);
            unascribe = (uu___108_1078.unascribe)
          }
      | UnfoldTac  ->
          let uu___109_1079 = fs  in
          {
            beta = (uu___109_1079.beta);
            iota = (uu___109_1079.iota);
            zeta = (uu___109_1079.zeta);
            weak = (uu___109_1079.weak);
            hnf = (uu___109_1079.hnf);
            primops = (uu___109_1079.primops);
            no_delta_steps = (uu___109_1079.no_delta_steps);
            unfold_until = (uu___109_1079.unfold_until);
            unfold_only = (uu___109_1079.unfold_only);
            unfold_attr = (uu___109_1079.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___109_1079.pure_subterms_within_computations);
            simplify = (uu___109_1079.simplify);
            erase_universes = (uu___109_1079.erase_universes);
            allow_unbound_universes = (uu___109_1079.allow_unbound_universes);
            reify_ = (uu___109_1079.reify_);
            compress_uvars = (uu___109_1079.compress_uvars);
            no_full_norm = (uu___109_1079.no_full_norm);
            check_no_uvars = (uu___109_1079.check_no_uvars);
            unmeta = (uu___109_1079.unmeta);
            unascribe = (uu___109_1079.unascribe)
          }
      | PureSubtermsWithinComputations  ->
          let uu___110_1080 = fs  in
          {
            beta = (uu___110_1080.beta);
            iota = (uu___110_1080.iota);
            zeta = (uu___110_1080.zeta);
            weak = (uu___110_1080.weak);
            hnf = (uu___110_1080.hnf);
            primops = (uu___110_1080.primops);
            no_delta_steps = (uu___110_1080.no_delta_steps);
            unfold_until = (uu___110_1080.unfold_until);
            unfold_only = (uu___110_1080.unfold_only);
            unfold_attr = (uu___110_1080.unfold_attr);
            unfold_tac = (uu___110_1080.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___110_1080.simplify);
            erase_universes = (uu___110_1080.erase_universes);
            allow_unbound_universes = (uu___110_1080.allow_unbound_universes);
            reify_ = (uu___110_1080.reify_);
            compress_uvars = (uu___110_1080.compress_uvars);
            no_full_norm = (uu___110_1080.no_full_norm);
            check_no_uvars = (uu___110_1080.check_no_uvars);
            unmeta = (uu___110_1080.unmeta);
            unascribe = (uu___110_1080.unascribe)
          }
      | Simplify  ->
          let uu___111_1081 = fs  in
          {
            beta = (uu___111_1081.beta);
            iota = (uu___111_1081.iota);
            zeta = (uu___111_1081.zeta);
            weak = (uu___111_1081.weak);
            hnf = (uu___111_1081.hnf);
            primops = (uu___111_1081.primops);
            no_delta_steps = (uu___111_1081.no_delta_steps);
            unfold_until = (uu___111_1081.unfold_until);
            unfold_only = (uu___111_1081.unfold_only);
            unfold_attr = (uu___111_1081.unfold_attr);
            unfold_tac = (uu___111_1081.unfold_tac);
            pure_subterms_within_computations =
              (uu___111_1081.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___111_1081.erase_universes);
            allow_unbound_universes = (uu___111_1081.allow_unbound_universes);
            reify_ = (uu___111_1081.reify_);
            compress_uvars = (uu___111_1081.compress_uvars);
            no_full_norm = (uu___111_1081.no_full_norm);
            check_no_uvars = (uu___111_1081.check_no_uvars);
            unmeta = (uu___111_1081.unmeta);
            unascribe = (uu___111_1081.unascribe)
          }
      | EraseUniverses  ->
          let uu___112_1082 = fs  in
          {
            beta = (uu___112_1082.beta);
            iota = (uu___112_1082.iota);
            zeta = (uu___112_1082.zeta);
            weak = (uu___112_1082.weak);
            hnf = (uu___112_1082.hnf);
            primops = (uu___112_1082.primops);
            no_delta_steps = (uu___112_1082.no_delta_steps);
            unfold_until = (uu___112_1082.unfold_until);
            unfold_only = (uu___112_1082.unfold_only);
            unfold_attr = (uu___112_1082.unfold_attr);
            unfold_tac = (uu___112_1082.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1082.pure_subterms_within_computations);
            simplify = (uu___112_1082.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___112_1082.allow_unbound_universes);
            reify_ = (uu___112_1082.reify_);
            compress_uvars = (uu___112_1082.compress_uvars);
            no_full_norm = (uu___112_1082.no_full_norm);
            check_no_uvars = (uu___112_1082.check_no_uvars);
            unmeta = (uu___112_1082.unmeta);
            unascribe = (uu___112_1082.unascribe)
          }
      | AllowUnboundUniverses  ->
          let uu___113_1083 = fs  in
          {
            beta = (uu___113_1083.beta);
            iota = (uu___113_1083.iota);
            zeta = (uu___113_1083.zeta);
            weak = (uu___113_1083.weak);
            hnf = (uu___113_1083.hnf);
            primops = (uu___113_1083.primops);
            no_delta_steps = (uu___113_1083.no_delta_steps);
            unfold_until = (uu___113_1083.unfold_until);
            unfold_only = (uu___113_1083.unfold_only);
            unfold_attr = (uu___113_1083.unfold_attr);
            unfold_tac = (uu___113_1083.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1083.pure_subterms_within_computations);
            simplify = (uu___113_1083.simplify);
            erase_universes = (uu___113_1083.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___113_1083.reify_);
            compress_uvars = (uu___113_1083.compress_uvars);
            no_full_norm = (uu___113_1083.no_full_norm);
            check_no_uvars = (uu___113_1083.check_no_uvars);
            unmeta = (uu___113_1083.unmeta);
            unascribe = (uu___113_1083.unascribe)
          }
      | Reify  ->
          let uu___114_1084 = fs  in
          {
            beta = (uu___114_1084.beta);
            iota = (uu___114_1084.iota);
            zeta = (uu___114_1084.zeta);
            weak = (uu___114_1084.weak);
            hnf = (uu___114_1084.hnf);
            primops = (uu___114_1084.primops);
            no_delta_steps = (uu___114_1084.no_delta_steps);
            unfold_until = (uu___114_1084.unfold_until);
            unfold_only = (uu___114_1084.unfold_only);
            unfold_attr = (uu___114_1084.unfold_attr);
            unfold_tac = (uu___114_1084.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1084.pure_subterms_within_computations);
            simplify = (uu___114_1084.simplify);
            erase_universes = (uu___114_1084.erase_universes);
            allow_unbound_universes = (uu___114_1084.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___114_1084.compress_uvars);
            no_full_norm = (uu___114_1084.no_full_norm);
            check_no_uvars = (uu___114_1084.check_no_uvars);
            unmeta = (uu___114_1084.unmeta);
            unascribe = (uu___114_1084.unascribe)
          }
      | CompressUvars  ->
          let uu___115_1085 = fs  in
          {
            beta = (uu___115_1085.beta);
            iota = (uu___115_1085.iota);
            zeta = (uu___115_1085.zeta);
            weak = (uu___115_1085.weak);
            hnf = (uu___115_1085.hnf);
            primops = (uu___115_1085.primops);
            no_delta_steps = (uu___115_1085.no_delta_steps);
            unfold_until = (uu___115_1085.unfold_until);
            unfold_only = (uu___115_1085.unfold_only);
            unfold_attr = (uu___115_1085.unfold_attr);
            unfold_tac = (uu___115_1085.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1085.pure_subterms_within_computations);
            simplify = (uu___115_1085.simplify);
            erase_universes = (uu___115_1085.erase_universes);
            allow_unbound_universes = (uu___115_1085.allow_unbound_universes);
            reify_ = (uu___115_1085.reify_);
            compress_uvars = true;
            no_full_norm = (uu___115_1085.no_full_norm);
            check_no_uvars = (uu___115_1085.check_no_uvars);
            unmeta = (uu___115_1085.unmeta);
            unascribe = (uu___115_1085.unascribe)
          }
      | NoFullNorm  ->
          let uu___116_1086 = fs  in
          {
            beta = (uu___116_1086.beta);
            iota = (uu___116_1086.iota);
            zeta = (uu___116_1086.zeta);
            weak = (uu___116_1086.weak);
            hnf = (uu___116_1086.hnf);
            primops = (uu___116_1086.primops);
            no_delta_steps = (uu___116_1086.no_delta_steps);
            unfold_until = (uu___116_1086.unfold_until);
            unfold_only = (uu___116_1086.unfold_only);
            unfold_attr = (uu___116_1086.unfold_attr);
            unfold_tac = (uu___116_1086.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1086.pure_subterms_within_computations);
            simplify = (uu___116_1086.simplify);
            erase_universes = (uu___116_1086.erase_universes);
            allow_unbound_universes = (uu___116_1086.allow_unbound_universes);
            reify_ = (uu___116_1086.reify_);
            compress_uvars = (uu___116_1086.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___116_1086.check_no_uvars);
            unmeta = (uu___116_1086.unmeta);
            unascribe = (uu___116_1086.unascribe)
          }
      | CheckNoUvars  ->
          let uu___117_1087 = fs  in
          {
            beta = (uu___117_1087.beta);
            iota = (uu___117_1087.iota);
            zeta = (uu___117_1087.zeta);
            weak = (uu___117_1087.weak);
            hnf = (uu___117_1087.hnf);
            primops = (uu___117_1087.primops);
            no_delta_steps = (uu___117_1087.no_delta_steps);
            unfold_until = (uu___117_1087.unfold_until);
            unfold_only = (uu___117_1087.unfold_only);
            unfold_attr = (uu___117_1087.unfold_attr);
            unfold_tac = (uu___117_1087.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1087.pure_subterms_within_computations);
            simplify = (uu___117_1087.simplify);
            erase_universes = (uu___117_1087.erase_universes);
            allow_unbound_universes = (uu___117_1087.allow_unbound_universes);
            reify_ = (uu___117_1087.reify_);
            compress_uvars = (uu___117_1087.compress_uvars);
            no_full_norm = (uu___117_1087.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___117_1087.unmeta);
            unascribe = (uu___117_1087.unascribe)
          }
      | Unmeta  ->
          let uu___118_1088 = fs  in
          {
            beta = (uu___118_1088.beta);
            iota = (uu___118_1088.iota);
            zeta = (uu___118_1088.zeta);
            weak = (uu___118_1088.weak);
            hnf = (uu___118_1088.hnf);
            primops = (uu___118_1088.primops);
            no_delta_steps = (uu___118_1088.no_delta_steps);
            unfold_until = (uu___118_1088.unfold_until);
            unfold_only = (uu___118_1088.unfold_only);
            unfold_attr = (uu___118_1088.unfold_attr);
            unfold_tac = (uu___118_1088.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1088.pure_subterms_within_computations);
            simplify = (uu___118_1088.simplify);
            erase_universes = (uu___118_1088.erase_universes);
            allow_unbound_universes = (uu___118_1088.allow_unbound_universes);
            reify_ = (uu___118_1088.reify_);
            compress_uvars = (uu___118_1088.compress_uvars);
            no_full_norm = (uu___118_1088.no_full_norm);
            check_no_uvars = (uu___118_1088.check_no_uvars);
            unmeta = true;
            unascribe = (uu___118_1088.unascribe)
          }
      | Unascribe  ->
          let uu___119_1089 = fs  in
          {
            beta = (uu___119_1089.beta);
            iota = (uu___119_1089.iota);
            zeta = (uu___119_1089.zeta);
            weak = (uu___119_1089.weak);
            hnf = (uu___119_1089.hnf);
            primops = (uu___119_1089.primops);
            no_delta_steps = (uu___119_1089.no_delta_steps);
            unfold_until = (uu___119_1089.unfold_until);
            unfold_only = (uu___119_1089.unfold_only);
            unfold_attr = (uu___119_1089.unfold_attr);
            unfold_tac = (uu___119_1089.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1089.pure_subterms_within_computations);
            simplify = (uu___119_1089.simplify);
            erase_universes = (uu___119_1089.erase_universes);
            allow_unbound_universes = (uu___119_1089.allow_unbound_universes);
            reify_ = (uu___119_1089.reify_);
            compress_uvars = (uu___119_1089.compress_uvars);
            no_full_norm = (uu___119_1089.no_full_norm);
            check_no_uvars = (uu___119_1089.check_no_uvars);
            unmeta = (uu___119_1089.unmeta);
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
             let uu____1752 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____1752 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____1764 = FStar_Util.psmap_empty ()  in add_steps uu____1764 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____1775 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____1775
  
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
    match projectee with | Arg _0 -> true | uu____1921 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____1957 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____1993 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2064 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,cfg,FStar_Range.range) FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2112 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2168 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2210 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2248 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2284 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2300 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2325 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2325 with | (hd1,uu____2339) -> hd1
  
let mk :
  'Auu____2359 .
    'Auu____2359 ->
      FStar_Range.range -> 'Auu____2359 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2413 = FStar_ST.op_Bang r  in
          match uu____2413 with
          | FStar_Pervasives_Native.Some uu____2461 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____2529 =
      FStar_List.map
        (fun uu____2543  ->
           match uu____2543 with
           | (bopt,c) ->
               let uu____2556 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____2558 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____2556 uu____2558) env
       in
    FStar_All.pipe_right uu____2529 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___79_2561  ->
    match uu___79_2561 with
    | Clos (env,t,uu____2564,uu____2565) ->
        let uu____2610 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____2617 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____2610 uu____2617
    | Univ uu____2618 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___80_2621  ->
    match uu___80_2621 with
    | Arg (c,uu____2623,uu____2624) ->
        let uu____2625 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2625
    | MemoLazy uu____2626 -> "MemoLazy"
    | Abs (uu____2633,bs,uu____2635,uu____2636,uu____2637) ->
        let uu____2642 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2642
    | UnivArgs uu____2647 -> "UnivArgs"
    | Match uu____2654 -> "Match"
    | App (uu____2663,t,uu____2665,uu____2666) ->
        let uu____2667 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2667
    | Meta (uu____2668,m,uu____2670) -> "Meta"
    | Let uu____2671 -> "Let"
    | Cfg uu____2680 -> "Cfg"
    | Debug (t,uu____2682) ->
        let uu____2683 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2683
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2691 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2691 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2722 . 'Auu____2722 Prims.list -> Prims.bool =
  fun uu___81_2728  ->
    match uu___81_2728 with | [] -> true | uu____2731 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        let uu____2759 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____2759
      with
      | uu____2778 ->
          let uu____2779 =
            let uu____2780 = FStar_Syntax_Print.db_to_string x  in
            let uu____2781 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____2780
              uu____2781
             in
          failwith uu____2779
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____2787 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____2787
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____2791 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____2791
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____2795 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____2795
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
          let uu____2821 =
            FStar_List.fold_left
              (fun uu____2847  ->
                 fun u1  ->
                   match uu____2847 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2872 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2872 with
                        | (k_u,n1) ->
                            let uu____2887 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____2887
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2821 with
          | (uu____2905,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____2930 =
                   let uu____2931 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____2931  in
                 match uu____2930 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____2949 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____2957 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____2963 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2972 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2981 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2988 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2988 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3005 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3005 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3013 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3021 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3021 with
                                  | (uu____3026,m) -> n1 <= m))
                           in
                        if uu____3013 then rest1 else us1
                    | uu____3031 -> us1)
               | uu____3036 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3040 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____3040
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3044 = aux u  in
           match uu____3044 with
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
          let t1 = FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____3149  ->
               let uu____3150 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____3151 = env_to_string env  in
               let uu____3152 = FStar_Syntax_Print.term_to_string t1  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3150 uu____3151 uu____3152);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.steps).compress_uvars
               -> rebuild_closure cfg env stack t1
           | uu____3161 ->
               (match t1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3164 ->
                    failwith "Impossible"
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_constant uu____3191 ->
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_name uu____3192 ->
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_lazy uu____3193 ->
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_fvar uu____3194 ->
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uvar uu____3195 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____3214 =
                        let uu____3215 =
                          FStar_Range.string_of_range
                            t1.FStar_Syntax_Syntax.pos
                           in
                        let uu____3216 = FStar_Syntax_Print.term_to_string t1
                           in
                        FStar_Util.format2
                          "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____3215 uu____3216
                         in
                      failwith uu____3214
                    else rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t2 =
                      let uu____3224 =
                        let uu____3225 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____3225  in
                      mk uu____3224 t1.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t2 =
                      let uu____3233 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3233  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____3235 = lookup_bvar env x  in
                    (match uu____3235 with
                     | Univ uu____3238 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___124_3242 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___124_3242.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___124_3242.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t2 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t1.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t2
                     | Clos (env1,t0,uu____3248,uu____3249) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____3334  ->
                              fun stack1  ->
                                match uu____3334 with
                                | (a,aq) ->
                                    let uu____3346 =
                                      let uu____3347 =
                                        let uu____3354 =
                                          let uu____3355 =
                                            let uu____3386 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____3386, false)  in
                                          Clos uu____3355  in
                                        (uu____3354, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____3347  in
                                    uu____3346 :: stack1) args)
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
                      (Abs
                         (env, bs, env', lopt, (t1.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    inline_closure_env cfg env' stack1 body
                | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                    let uu____3580 = close_binders cfg env bs  in
                    (match uu____3580 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t2 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t1.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t2)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____3627 =
                      let uu____3638 =
                        let uu____3645 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____3645]  in
                      close_binders cfg env uu____3638  in
                    (match uu____3627 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t2 =
                           let uu____3668 =
                             let uu____3669 =
                               let uu____3676 =
                                 let uu____3677 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____3677
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____3676, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____3669  in
                           mk uu____3668 t1.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t2)
                | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt)
                    ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____3768 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____3768
                      | FStar_Util.Inr c ->
                          let uu____3782 = close_comp cfg env c  in
                          FStar_Util.Inr uu____3782
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____3801 =
                        let uu____3802 =
                          let uu____3829 =
                            non_tail_inline_closure_env cfg env t11  in
                          (uu____3829, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____3802  in
                      mk uu____3801 t1.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t2 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____3875 =
                            let uu____3876 =
                              let uu____3883 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____3883, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____3876  in
                          mk uu____3875 t1.FStar_Syntax_Syntax.pos
                      | FStar_Syntax_Syntax.Quote_static  ->
                          let qi1 =
                            FStar_Syntax_Syntax.on_antiquoted
                              (non_tail_inline_closure_env cfg env) qi
                             in
                          mk (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                            t1.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                    let stack1 =
                      (Meta (env, m, (t1.FStar_Syntax_Syntax.pos))) :: stack
                       in
                    inline_closure_env cfg env stack1 t'
                | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                    let env0 = env  in
                    let env1 =
                      FStar_List.fold_left
                        (fun env1  -> fun uu____3935  -> dummy :: env1) env
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
                    let uu____3956 =
                      let uu____3967 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____3967
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____3986 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___125_4002 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___125_4002.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___125_4002.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____3986))
                       in
                    (match uu____3956 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___126_4020 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___126_4020.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___126_4020.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___126_4020.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___126_4020.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t2 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t1.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env1 stack t2)
                | FStar_Syntax_Syntax.Tm_let ((uu____4034,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____4093  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____4118 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4118
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____4138  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____4162 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____4162
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___127_4170 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___127_4170.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___127_4170.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___128_4171 = lb  in
                      let uu____4172 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___128_4171.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___128_4171.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____4172;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___128_4171.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___128_4171.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____4204  -> fun env1  -> dummy :: env1)
                          lbs1 env
                         in
                      non_tail_inline_closure_env cfg body_env body  in
                    let t2 =
                      mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                        t1.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                    let stack1 =
                      (Match
                         (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
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
            (fun uu____4307  ->
               let uu____4308 = FStar_Syntax_Print.tag_of_term t  in
               let uu____4309 = env_to_string env  in
               let uu____4310 = stack_to_string stack  in
               let uu____4311 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____4308 uu____4309 uu____4310 uu____4311);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____4316,uu____4317),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____4392 = close_binders cfg env' bs  in
               (match uu____4392 with
                | (bs1,uu____4406) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____4422 =
                      let uu___129_4423 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___129_4423.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___129_4423.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____4422)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____4465 =
                 match uu____4465 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____4536 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____4557 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____4617  ->
                                     fun uu____4618  ->
                                       match (uu____4617, uu____4618) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____4709 = norm_pat env4 p1
                                              in
                                           (match uu____4709 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____4557 with
                            | (pats1,env4) ->
                                ((let uu___130_4791 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___130_4791.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___131_4810 = x  in
                             let uu____4811 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___131_4810.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___131_4810.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4811
                             }  in
                           ((let uu___132_4825 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___132_4825.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___133_4836 = x  in
                             let uu____4837 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___133_4836.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___133_4836.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4837
                             }  in
                           ((let uu___134_4851 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___134_4851.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___135_4867 = x  in
                             let uu____4868 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___135_4867.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___135_4867.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4868
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___136_4877 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___136_4877.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____4882 = norm_pat env2 pat  in
                     (match uu____4882 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____4927 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____4927
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____4946 =
                   let uu____4947 =
                     let uu____4970 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____4970)  in
                   FStar_Syntax_Syntax.Tm_match uu____4947  in
                 mk uu____4946 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____5065 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____5154  ->
                                       match uu____5154 with
                                       | (a,q) ->
                                           let uu____5173 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____5173, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____5065
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____5184 =
                       let uu____5191 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____5191)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____5184
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____5203 =
                       let uu____5212 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____5212)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____5203
                 | uu____5217 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____5221 -> failwith "Impossible: unexpected stack element")

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
        let uu____5235 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____5284  ->
                  fun uu____5285  ->
                    match (uu____5284, uu____5285) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___137_5355 = b  in
                          let uu____5356 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___137_5355.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___137_5355.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____5356
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____5235 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____5449 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5462 = inline_closure_env cfg env [] t  in
                 let uu____5463 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5462 uu____5463
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5476 = inline_closure_env cfg env [] t  in
                 let uu____5477 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5476 uu____5477
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____5523  ->
                           match uu____5523 with
                           | (a,q) ->
                               let uu____5536 =
                                 inline_closure_env cfg env [] a  in
                               (uu____5536, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___82_5551  ->
                           match uu___82_5551 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5555 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____5555
                           | f -> f))
                    in
                 let uu____5559 =
                   let uu___138_5560 = c1  in
                   let uu____5561 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5561;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___138_5560.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5559)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___83_5571  ->
            match uu___83_5571 with
            | FStar_Syntax_Syntax.DECREASES uu____5572 -> false
            | uu____5575 -> true))

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
                   (fun uu___84_5593  ->
                      match uu___84_5593 with
                      | FStar_Syntax_Syntax.DECREASES uu____5594 -> false
                      | uu____5597 -> true))
               in
            let rc1 =
              let uu___139_5599 = rc  in
              let uu____5600 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___139_5599.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5600;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5609 -> lopt

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
  let arg_as_list a e a =
    let uu____5700 =
      let uu____5707 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____5707  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5700  in
  let arg_as_bounded_int uu____5731 =
    match uu____5731 with
    | (a,uu____5743) ->
        let uu____5750 =
          let uu____5751 = FStar_Syntax_Subst.compress a  in
          uu____5751.FStar_Syntax_Syntax.n  in
        (match uu____5750 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5761;
                FStar_Syntax_Syntax.vars = uu____5762;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5764;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5765;_},uu____5766)::[])
             when
             let uu____5805 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____5805 "int_to_t" ->
             let uu____5806 =
               let uu____5811 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5811)  in
             FStar_Pervasives_Native.Some uu____5806
         | uu____5816 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5856 = f a  in FStar_Pervasives_Native.Some uu____5856
    | uu____5857 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5905 = f a0 a1  in FStar_Pervasives_Native.Some uu____5905
    | uu____5906 -> FStar_Pervasives_Native.None  in
  let unary_op a394 a395 a396 a397 a398 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5948 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a393  -> (Obj.magic (f res.psc_range)) a393)
                    uu____5948)) a394 a395 a396 a397 a398
     in
  let binary_op a401 a402 a403 a404 a405 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5997 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a399  ->
                       fun a400  -> (Obj.magic (f res.psc_range)) a399 a400)
                    uu____5997)) a401 a402 a403 a404 a405
     in
  let as_primitive_step is_strong uu____6024 =
    match uu____6024 with
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
    unary_op () (fun a406  -> (Obj.magic arg_as_int) a406)
      (fun a407  ->
         fun a408  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____6072 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_int r uu____6072)) a407 a408)
     in
  let binary_int_op f =
    binary_op () (fun a409  -> (Obj.magic arg_as_int) a409)
      (fun a410  ->
         fun a411  ->
           fun a412  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6100 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_int r uu____6100)) a410
               a411 a412)
     in
  let unary_bool_op f =
    unary_op () (fun a413  -> (Obj.magic arg_as_bool) a413)
      (fun a414  ->
         fun a415  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____6121 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_bool r uu____6121)) a414 a415)
     in
  let binary_bool_op f =
    binary_op () (fun a416  -> (Obj.magic arg_as_bool) a416)
      (fun a417  ->
         fun a418  ->
           fun a419  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6149 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_bool r uu____6149)) a417
               a418 a419)
     in
  let binary_string_op f =
    binary_op () (fun a420  -> (Obj.magic arg_as_string) a420)
      (fun a421  ->
         fun a422  ->
           fun a423  ->
             (Obj.magic
                (fun r  ->
                   fun x  ->
                     fun y  ->
                       let uu____6177 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_string r uu____6177)) a421
               a422 a423)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____6285 =
          let uu____6294 = as_a a  in
          let uu____6297 = as_b b  in (uu____6294, uu____6297)  in
        (match uu____6285 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____6312 =
               let uu____6313 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____6313  in
             FStar_Pervasives_Native.Some uu____6312
         | uu____6314 -> FStar_Pervasives_Native.None)
    | uu____6323 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____6337 =
        let uu____6338 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____6338  in
      mk uu____6337 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____6348 =
      let uu____6351 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____6351  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____6348  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____6383 =
      let uu____6384 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____6384  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____6383
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____6402 = arg_as_string a1  in
        (match uu____6402 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6408 =
               Obj.magic
                 (arg_as_list () (Obj.magic FStar_Syntax_Embeddings.e_string)
                    a2)
                in
             (match uu____6408 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____6421 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____6421
              | uu____6422 -> FStar_Pervasives_Native.None)
         | uu____6427 -> FStar_Pervasives_Native.None)
    | uu____6430 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____6440 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____6440
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6469 =
          let uu____6490 = arg_as_string fn  in
          let uu____6493 = arg_as_int from_line  in
          let uu____6496 = arg_as_int from_col  in
          let uu____6499 = arg_as_int to_line  in
          let uu____6502 = arg_as_int to_col  in
          (uu____6490, uu____6493, uu____6496, uu____6499, uu____6502)  in
        (match uu____6469 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6533 =
                 let uu____6534 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6535 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6534 uu____6535  in
               let uu____6536 =
                 let uu____6537 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6538 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6537 uu____6538  in
               FStar_Range.mk_range fn1 uu____6533 uu____6536  in
             let uu____6539 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6539
         | uu____6540 -> FStar_Pervasives_Native.None)
    | uu____6561 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6588)::(a1,uu____6590)::(a2,uu____6592)::[] ->
        let uu____6629 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6629 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6642 -> FStar_Pervasives_Native.None)
    | uu____6643 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____6670)::[] ->
        let uu____6679 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____6679 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6685 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6685
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6686 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6710 =
      let uu____6725 =
        let uu____6740 =
          let uu____6755 =
            let uu____6770 =
              let uu____6785 =
                let uu____6800 =
                  let uu____6815 =
                    let uu____6830 =
                      let uu____6845 =
                        let uu____6860 =
                          let uu____6875 =
                            let uu____6890 =
                              let uu____6905 =
                                let uu____6920 =
                                  let uu____6935 =
                                    let uu____6950 =
                                      let uu____6965 =
                                        let uu____6980 =
                                          let uu____6995 =
                                            let uu____7010 =
                                              let uu____7025 =
                                                let uu____7038 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____7038,
                                                  (Prims.parse_int "1"),
                                                  (unary_op ()
                                                     (fun a424  ->
                                                        (Obj.magic
                                                           arg_as_string)
                                                          a424)
                                                     (fun a425  ->
                                                        fun a426  ->
                                                          (Obj.magic
                                                             list_of_string')
                                                            a425 a426)))
                                                 in
                                              let uu____7045 =
                                                let uu____7060 =
                                                  let uu____7073 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____7073,
                                                    (Prims.parse_int "1"),
                                                    (unary_op ()
                                                       (fun a427  ->
                                                          (Obj.magic
                                                             (arg_as_list ()
                                                                (Obj.magic
                                                                   FStar_Syntax_Embeddings.e_char)))
                                                            a427)
                                                       (fun a428  ->
                                                          fun a429  ->
                                                            (Obj.magic
                                                               string_of_list')
                                                              a428 a429)))
                                                   in
                                                let uu____7080 =
                                                  let uu____7095 =
                                                    let uu____7110 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____7110,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____7119 =
                                                    let uu____7136 =
                                                      let uu____7151 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____7151,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____7136]  in
                                                  uu____7095 :: uu____7119
                                                   in
                                                uu____7060 :: uu____7080  in
                                              uu____7025 :: uu____7045  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____7010
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6995
                                           in
                                        (FStar_Parser_Const.string_compare,
                                          (Prims.parse_int "2"),
                                          (binary_op ()
                                             (fun a430  ->
                                                (Obj.magic arg_as_string)
                                                  a430)
                                             (fun a431  ->
                                                fun a432  ->
                                                  fun a433  ->
                                                    (Obj.magic
                                                       string_compare') a431
                                                      a432 a433)))
                                          :: uu____6980
                                         in
                                      (FStar_Parser_Const.string_of_bool_lid,
                                        (Prims.parse_int "1"),
                                        (unary_op ()
                                           (fun a434  ->
                                              (Obj.magic arg_as_bool) a434)
                                           (fun a435  ->
                                              fun a436  ->
                                                (Obj.magic string_of_bool1)
                                                  a435 a436)))
                                        :: uu____6965
                                       in
                                    (FStar_Parser_Const.string_of_int_lid,
                                      (Prims.parse_int "1"),
                                      (unary_op ()
                                         (fun a437  ->
                                            (Obj.magic arg_as_int) a437)
                                         (fun a438  ->
                                            fun a439  ->
                                              (Obj.magic string_of_int1) a438
                                                a439)))
                                      :: uu____6950
                                     in
                                  (FStar_Parser_Const.str_make_lid,
                                    (Prims.parse_int "2"),
                                    (mixed_binary_op () () ()
                                       (fun a440  ->
                                          (Obj.magic arg_as_int) a440)
                                       (fun a441  ->
                                          (Obj.magic arg_as_char) a441)
                                       (fun a442  ->
                                          fun a443  ->
                                            (Obj.magic
                                               (FStar_Syntax_Embeddings.embed
                                                  FStar_Syntax_Embeddings.e_string))
                                              a442 a443)
                                       (fun a444  ->
                                          fun a445  ->
                                            fun a446  ->
                                              (Obj.magic
                                                 (fun r  ->
                                                    fun x  ->
                                                      fun y  ->
                                                        let uu____7342 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____7342 y)) a444
                                                a445 a446)))
                                    :: uu____6935
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6920
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6905
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6890
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6875
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6860
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6845
                       in
                    (FStar_Parser_Const.op_GTE, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a447  -> (Obj.magic arg_as_int) a447)
                         (fun a448  ->
                            fun a449  ->
                              fun a450  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun x  ->
                                        fun y  ->
                                          let uu____7509 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed
                                            FStar_Syntax_Embeddings.e_bool r
                                            uu____7509)) a448 a449 a450)))
                      :: uu____6830
                     in
                  (FStar_Parser_Const.op_GT, (Prims.parse_int "2"),
                    (binary_op () (fun a451  -> (Obj.magic arg_as_int) a451)
                       (fun a452  ->
                          fun a453  ->
                            fun a454  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun x  ->
                                      fun y  ->
                                        let uu____7535 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_bool r
                                          uu____7535)) a452 a453 a454)))
                    :: uu____6815
                   in
                (FStar_Parser_Const.op_LTE, (Prims.parse_int "2"),
                  (binary_op () (fun a455  -> (Obj.magic arg_as_int) a455)
                     (fun a456  ->
                        fun a457  ->
                          fun a458  ->
                            (Obj.magic
                               (fun r  ->
                                  fun x  ->
                                    fun y  ->
                                      let uu____7561 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed
                                        FStar_Syntax_Embeddings.e_bool r
                                        uu____7561)) a456 a457 a458)))
                  :: uu____6800
                 in
              (FStar_Parser_Const.op_LT, (Prims.parse_int "2"),
                (binary_op () (fun a459  -> (Obj.magic arg_as_int) a459)
                   (fun a460  ->
                      fun a461  ->
                        fun a462  ->
                          (Obj.magic
                             (fun r  ->
                                fun x  ->
                                  fun y  ->
                                    let uu____7587 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_bool r
                                      uu____7587)) a460 a461 a462)))
                :: uu____6785
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6770
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6755
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6740
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6725
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6710
     in
  let weak_ops =
    let uu____7726 =
      let uu____7745 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____7745, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____7726]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7829 =
        let uu____7830 =
          let uu____7831 = FStar_Syntax_Syntax.as_arg c  in [uu____7831]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7830  in
      uu____7829 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7881 =
                let uu____7894 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7894, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a463  -> (Obj.magic arg_as_bounded_int) a463)
                     (fun a464  ->
                        fun a465  ->
                          fun a466  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7910  ->
                                    fun uu____7911  ->
                                      match (uu____7910, uu____7911) with
                                      | ((int_to_t1,x),(uu____7930,y)) ->
                                          let uu____7940 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7940)) a464 a465 a466)))
                 in
              let uu____7941 =
                let uu____7956 =
                  let uu____7969 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7969, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a467  -> (Obj.magic arg_as_bounded_int) a467)
                       (fun a468  ->
                          fun a469  ->
                            fun a470  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7985  ->
                                      fun uu____7986  ->
                                        match (uu____7985, uu____7986) with
                                        | ((int_to_t1,x),(uu____8005,y)) ->
                                            let uu____8015 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____8015)) a468 a469 a470)))
                   in
                let uu____8016 =
                  let uu____8031 =
                    let uu____8044 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____8044, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a471  -> (Obj.magic arg_as_bounded_int) a471)
                         (fun a472  ->
                            fun a473  ->
                              fun a474  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____8060  ->
                                        fun uu____8061  ->
                                          match (uu____8060, uu____8061) with
                                          | ((int_to_t1,x),(uu____8080,y)) ->
                                              let uu____8090 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____8090)) a472 a473 a474)))
                     in
                  let uu____8091 =
                    let uu____8106 =
                      let uu____8119 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____8119, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a475  -> (Obj.magic arg_as_bounded_int) a475)
                           (fun a476  ->
                              fun a477  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____8131  ->
                                        match uu____8131 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed
                                              FStar_Syntax_Embeddings.e_int r
                                              x)) a476 a477)))
                       in
                    [uu____8106]  in
                  uu____8031 :: uu____8091  in
                uu____7956 :: uu____8016  in
              uu____7881 :: uu____7941))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____8245 =
                let uu____8258 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____8258, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a478  -> (Obj.magic arg_as_bounded_int) a478)
                     (fun a479  ->
                        fun a480  ->
                          fun a481  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____8274  ->
                                    fun uu____8275  ->
                                      match (uu____8274, uu____8275) with
                                      | ((int_to_t1,x),(uu____8294,y)) ->
                                          let uu____8304 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____8304)) a479 a480 a481)))
                 in
              let uu____8305 =
                let uu____8320 =
                  let uu____8333 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____8333, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a482  -> (Obj.magic arg_as_bounded_int) a482)
                       (fun a483  ->
                          fun a484  ->
                            fun a485  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____8349  ->
                                      fun uu____8350  ->
                                        match (uu____8349, uu____8350) with
                                        | ((int_to_t1,x),(uu____8369,y)) ->
                                            let uu____8379 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____8379)) a483 a484 a485)))
                   in
                [uu____8320]  in
              uu____8245 :: uu____8305))
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
    | (_typ,uu____8491)::(a1,uu____8493)::(a2,uu____8495)::[] ->
        let uu____8532 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8532 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___140_8538 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___140_8538.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___140_8538.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___141_8542 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_8542.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_8542.FStar_Syntax_Syntax.vars)
                })
         | uu____8543 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8545)::uu____8546::(a1,uu____8548)::(a2,uu____8550)::[] ->
        let uu____8599 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8599 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___140_8605 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___140_8605.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___140_8605.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___141_8609 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___141_8609.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___141_8609.FStar_Syntax_Syntax.vars)
                })
         | uu____8610 -> FStar_Pervasives_Native.None)
    | uu____8611 -> failwith "Unexpected number of arguments"  in
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
    let uu____8663 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____8663 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____8708 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8708) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8768  ->
           fun subst1  ->
             match uu____8768 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8809,uu____8810)) ->
                      let uu____8869 = b  in
                      (match uu____8869 with
                       | (bv,uu____8877) ->
                           let uu____8878 =
                             let uu____8879 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____8879  in
                           if uu____8878
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8884 = unembed_binder term1  in
                              match uu____8884 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8891 =
                                      let uu___142_8892 = bv  in
                                      let uu____8893 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___142_8892.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___142_8892.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8893
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8891
                                     in
                                  let b_for_x =
                                    let uu____8897 =
                                      let uu____8904 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8904)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8897  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___85_8914  ->
                                         match uu___85_8914 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8915,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8917;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8918;_})
                                             ->
                                             let uu____8923 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____8923
                                         | uu____8924 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8925 -> subst1)) env []
  
let reduce_primops :
  'Auu____8942 'Auu____8943 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8942) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8943 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8985 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8985 with
             | (head1,args) ->
                 let uu____9022 =
                   let uu____9023 = FStar_Syntax_Util.un_uinst head1  in
                   uu____9023.FStar_Syntax_Syntax.n  in
                 (match uu____9022 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____9027 = find_prim_step cfg fv  in
                      (match uu____9027 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____9049  ->
                                   let uu____9050 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____9051 =
                                     FStar_Util.string_of_int l  in
                                   let uu____9058 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____9050 uu____9051 uu____9058);
                              tm)
                           else
                             (let uu____9060 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____9060 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____9171  ->
                                        let uu____9172 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____9172);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____9175  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____9177 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____9177 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____9183  ->
                                              let uu____9184 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____9184);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____9190  ->
                                              let uu____9191 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____9192 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____9191 uu____9192);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____9193 ->
                           (log_primops cfg
                              (fun uu____9197  ->
                                 let uu____9198 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____9198);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____9202  ->
                            let uu____9203 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____9203);
                       (match args with
                        | (a1,uu____9205)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____9222 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____9234  ->
                            let uu____9235 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____9235);
                       (match args with
                        | (t,uu____9237)::(r,uu____9239)::[] ->
                            let uu____9266 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____9266 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___143_9270 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___143_9270.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___143_9270.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____9273 -> tm))
                  | uu____9282 -> tm))
  
let reduce_equality :
  'Auu____9287 'Auu____9288 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____9287) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____9288 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___144_9326 = cfg  in
         {
           steps =
             (let uu___145_9329 = default_steps  in
              {
                beta = (uu___145_9329.beta);
                iota = (uu___145_9329.iota);
                zeta = (uu___145_9329.zeta);
                weak = (uu___145_9329.weak);
                hnf = (uu___145_9329.hnf);
                primops = true;
                no_delta_steps = (uu___145_9329.no_delta_steps);
                unfold_until = (uu___145_9329.unfold_until);
                unfold_only = (uu___145_9329.unfold_only);
                unfold_attr = (uu___145_9329.unfold_attr);
                unfold_tac = (uu___145_9329.unfold_tac);
                pure_subterms_within_computations =
                  (uu___145_9329.pure_subterms_within_computations);
                simplify = (uu___145_9329.simplify);
                erase_universes = (uu___145_9329.erase_universes);
                allow_unbound_universes =
                  (uu___145_9329.allow_unbound_universes);
                reify_ = (uu___145_9329.reify_);
                compress_uvars = (uu___145_9329.compress_uvars);
                no_full_norm = (uu___145_9329.no_full_norm);
                check_no_uvars = (uu___145_9329.check_no_uvars);
                unmeta = (uu___145_9329.unmeta);
                unascribe = (uu___145_9329.unascribe)
              });
           tcenv = (uu___144_9326.tcenv);
           debug = (uu___144_9326.debug);
           delta_level = (uu___144_9326.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___144_9326.strong);
           memoize_lazy = (uu___144_9326.memoize_lazy);
           normalize_pure_lets = (uu___144_9326.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____9333 .
    FStar_Syntax_Syntax.term -> 'Auu____9333 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____9346 =
        let uu____9353 =
          let uu____9354 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9354.FStar_Syntax_Syntax.n  in
        (uu____9353, args)  in
      match uu____9346 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9360::uu____9361::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9365::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____9370::uu____9371::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____9374 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___86_9385  ->
    match uu___86_9385 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____9391 =
          let uu____9394 =
            let uu____9395 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldOnly uu____9395  in
          [uu____9394]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____9391
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____9411 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____9411) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____9453 =
          let uu____9458 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____9458 s  in
        match uu____9453 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____9474 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____9474
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____9491::(tm,uu____9493)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____9522)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____9543)::uu____9544::(tm,uu____9546)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____9583 =
            let uu____9588 = full_norm steps  in parse_steps uu____9588  in
          (match uu____9583 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____9627 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___87_9644  ->
    match uu___87_9644 with
    | (App
        (uu____9647,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____9648;
                      FStar_Syntax_Syntax.vars = uu____9649;_},uu____9650,uu____9651))::uu____9652
        -> true
    | uu____9659 -> false
  
let firstn :
  'Auu____9665 .
    Prims.int ->
      'Auu____9665 Prims.list ->
        ('Auu____9665 Prims.list,'Auu____9665 Prims.list)
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
          (uu____9701,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____9702;
                        FStar_Syntax_Syntax.vars = uu____9703;_},uu____9704,uu____9705))::uu____9706
          -> (cfg.steps).reify_
      | uu____9713 -> false
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9897 ->
                   let uu____9922 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9922
               | uu____9923 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____9931  ->
               let uu____9932 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9933 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9934 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9941 =
                 let uu____9942 =
                   let uu____9945 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9945
                    in
                 stack_to_string uu____9942  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____9932 uu____9933 uu____9934 uu____9941);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____9968 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____9969 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____9970 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9971;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____9972;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9975;
                 FStar_Syntax_Syntax.fv_delta = uu____9976;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9977;
                 FStar_Syntax_Syntax.fv_delta = uu____9978;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9979);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____9986 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____10022 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____10022)
               ->
               let cfg' =
                 let uu___146_10024 = cfg  in
                 {
                   steps =
                     (let uu___147_10027 = cfg.steps  in
                      {
                        beta = (uu___147_10027.beta);
                        iota = (uu___147_10027.iota);
                        zeta = (uu___147_10027.zeta);
                        weak = (uu___147_10027.weak);
                        hnf = (uu___147_10027.hnf);
                        primops = (uu___147_10027.primops);
                        no_delta_steps = false;
                        unfold_until = (uu___147_10027.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___147_10027.unfold_attr);
                        unfold_tac = (uu___147_10027.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___147_10027.pure_subterms_within_computations);
                        simplify = (uu___147_10027.simplify);
                        erase_universes = (uu___147_10027.erase_universes);
                        allow_unbound_universes =
                          (uu___147_10027.allow_unbound_universes);
                        reify_ = (uu___147_10027.reify_);
                        compress_uvars = (uu___147_10027.compress_uvars);
                        no_full_norm = (uu___147_10027.no_full_norm);
                        check_no_uvars = (uu___147_10027.check_no_uvars);
                        unmeta = (uu___147_10027.unmeta);
                        unascribe = (uu___147_10027.unascribe)
                      });
                   tcenv = (uu___146_10024.tcenv);
                   debug = (uu___146_10024.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___146_10024.primitive_steps);
                   strong = (uu___146_10024.strong);
                   memoize_lazy = (uu___146_10024.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____10030 = get_norm_request (norm cfg' env []) args  in
               (match uu____10030 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____10061  ->
                              fun stack1  ->
                                match uu____10061 with
                                | (a,aq) ->
                                    let uu____10073 =
                                      let uu____10074 =
                                        let uu____10081 =
                                          let uu____10082 =
                                            let uu____10113 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____10113, false)  in
                                          Clos uu____10082  in
                                        (uu____10081, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____10074  in
                                    uu____10073 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____10197  ->
                          let uu____10198 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____10198);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____10220 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___88_10225  ->
                                match uu___88_10225 with
                                | UnfoldUntil uu____10226 -> true
                                | UnfoldOnly uu____10227 -> true
                                | uu____10230 -> false))
                         in
                      if uu____10220
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___148_10235 = cfg  in
                      let uu____10236 = to_fsteps s  in
                      {
                        steps = uu____10236;
                        tcenv = (uu___148_10235.tcenv);
                        debug = (uu___148_10235.debug);
                        delta_level;
                        primitive_steps = (uu___148_10235.primitive_steps);
                        strong = (uu___148_10235.strong);
                        memoize_lazy = (uu___148_10235.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____10245 =
                          let uu____10246 =
                            let uu____10251 = FStar_Util.now ()  in
                            (t1, uu____10251)  in
                          Debug uu____10246  in
                        uu____10245 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____10255 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10255
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10264 =
                      let uu____10271 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____10271, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10264  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____10281 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____10281  in
               let uu____10282 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____10282
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____10288  ->
                       let uu____10289 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10290 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____10289 uu____10290);
                  if b
                  then
                    (let uu____10291 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____10291 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    (let uu____10299 = find_prim_step cfg fv  in
                     FStar_Option.isNone uu____10299) &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___89_10305  ->
                               match uu___89_10305 with
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
                          (let uu____10315 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____10315))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____10334) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____10369,uu____10370) -> false)))
                     in
                  log cfg
                    (fun uu____10392  ->
                       let uu____10393 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10394 =
                         FStar_Range.string_of_range
                           t1.FStar_Syntax_Syntax.pos
                          in
                       let uu____10395 =
                         FStar_Util.string_of_bool should_delta1  in
                       FStar_Util.print3
                         ">>> For %s (%s), should_delta = %s\n" uu____10393
                         uu____10394 uu____10395);
                  if should_delta1
                  then do_unfold_fv cfg env stack t1 qninfo fv
                  else rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10398 = lookup_bvar env x  in
               (match uu____10398 with
                | Univ uu____10399 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____10448 = FStar_ST.op_Bang r  in
                      (match uu____10448 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____10566  ->
                                 let uu____10567 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10568 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10567
                                   uu____10568);
                            (let uu____10569 =
                               let uu____10570 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____10570.FStar_Syntax_Syntax.n  in
                             match uu____10569 with
                             | FStar_Syntax_Syntax.Tm_abs uu____10573 ->
                                 norm cfg env2 stack t'
                             | uu____10590 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10660)::uu____10661 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____10670)::uu____10671 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____10683,uu____10684))::stack_rest ->
                    (match c with
                     | Univ uu____10688 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10697 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____10718  ->
                                    let uu____10719 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10719);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____10759  ->
                                    let uu____10760 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10760);
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
                       (fun uu____10838  ->
                          let uu____10839 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10839);
                     norm cfg env stack1 t1)
                | (Debug uu____10840)::uu____10841 ->
                    if (cfg.steps).weak
                    then
                      let uu____10848 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10848
                    else
                      (let uu____10850 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10850 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10892  -> dummy :: env1) env)
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
                                          let uu____10929 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10929)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_10934 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_10934.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_10934.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10935 -> lopt  in
                           (log cfg
                              (fun uu____10941  ->
                                 let uu____10942 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10942);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_10951 = cfg  in
                               {
                                 steps = (uu___150_10951.steps);
                                 tcenv = (uu___150_10951.tcenv);
                                 debug = (uu___150_10951.debug);
                                 delta_level = (uu___150_10951.delta_level);
                                 primitive_steps =
                                   (uu___150_10951.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_10951.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_10951.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10962)::uu____10963 ->
                    if (cfg.steps).weak
                    then
                      let uu____10972 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10972
                    else
                      (let uu____10974 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10974 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11016  -> dummy :: env1) env)
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
                                          let uu____11053 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11053)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_11058 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_11058.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_11058.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11059 -> lopt  in
                           (log cfg
                              (fun uu____11065  ->
                                 let uu____11066 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11066);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_11075 = cfg  in
                               {
                                 steps = (uu___150_11075.steps);
                                 tcenv = (uu___150_11075.tcenv);
                                 debug = (uu___150_11075.debug);
                                 delta_level = (uu___150_11075.delta_level);
                                 primitive_steps =
                                   (uu___150_11075.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_11075.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_11075.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11086)::uu____11087 ->
                    if (cfg.steps).weak
                    then
                      let uu____11098 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11098
                    else
                      (let uu____11100 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11100 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11142  -> dummy :: env1) env)
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
                                          let uu____11179 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11179)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_11184 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_11184.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_11184.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11185 -> lopt  in
                           (log cfg
                              (fun uu____11191  ->
                                 let uu____11192 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11192);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_11201 = cfg  in
                               {
                                 steps = (uu___150_11201.steps);
                                 tcenv = (uu___150_11201.tcenv);
                                 debug = (uu___150_11201.debug);
                                 delta_level = (uu___150_11201.delta_level);
                                 primitive_steps =
                                   (uu___150_11201.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_11201.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_11201.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11212)::uu____11213 ->
                    if (cfg.steps).weak
                    then
                      let uu____11224 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11224
                    else
                      (let uu____11226 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11226 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11268  -> dummy :: env1) env)
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
                                          let uu____11305 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11305)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_11310 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_11310.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_11310.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11311 -> lopt  in
                           (log cfg
                              (fun uu____11317  ->
                                 let uu____11318 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11318);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_11327 = cfg  in
                               {
                                 steps = (uu___150_11327.steps);
                                 tcenv = (uu___150_11327.tcenv);
                                 debug = (uu___150_11327.debug);
                                 delta_level = (uu___150_11327.delta_level);
                                 primitive_steps =
                                   (uu___150_11327.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_11327.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_11327.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11338)::uu____11339 ->
                    if (cfg.steps).weak
                    then
                      let uu____11354 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11354
                    else
                      (let uu____11356 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11356 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11398  -> dummy :: env1) env)
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
                                          let uu____11435 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11435)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_11440 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_11440.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_11440.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11441 -> lopt  in
                           (log cfg
                              (fun uu____11447  ->
                                 let uu____11448 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11448);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_11457 = cfg  in
                               {
                                 steps = (uu___150_11457.steps);
                                 tcenv = (uu___150_11457.tcenv);
                                 debug = (uu___150_11457.debug);
                                 delta_level = (uu___150_11457.delta_level);
                                 primitive_steps =
                                   (uu___150_11457.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_11457.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_11457.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____11468 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11468
                    else
                      (let uu____11470 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11470 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11512  -> dummy :: env1) env)
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
                                          let uu____11549 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11549)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___149_11554 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___149_11554.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___149_11554.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11555 -> lopt  in
                           (log cfg
                              (fun uu____11561  ->
                                 let uu____11562 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11562);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___150_11571 = cfg  in
                               {
                                 steps = (uu___150_11571.steps);
                                 tcenv = (uu___150_11571.tcenv);
                                 debug = (uu___150_11571.debug);
                                 delta_level = (uu___150_11571.delta_level);
                                 primitive_steps =
                                   (uu___150_11571.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___150_11571.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___150_11571.normalize_pure_lets)
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
                      (fun uu____11620  ->
                         fun stack1  ->
                           match uu____11620 with
                           | (a,aq) ->
                               let uu____11632 =
                                 let uu____11633 =
                                   let uu____11640 =
                                     let uu____11641 =
                                       let uu____11672 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____11672, false)  in
                                     Clos uu____11641  in
                                   (uu____11640, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____11633  in
                               uu____11632 :: stack1) args)
                  in
               (log cfg
                  (fun uu____11756  ->
                     let uu____11757 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____11757);
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
                             ((let uu___151_11793 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___151_11793.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___151_11793.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____11794 ->
                      let uu____11799 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11799)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____11802 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____11802 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____11833 =
                          let uu____11834 =
                            let uu____11841 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___152_11843 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___152_11843.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___152_11843.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____11841)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____11834  in
                        mk uu____11833 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____11862 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____11862
               else
                 (let uu____11864 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____11864 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____11872 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____11896  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____11872 c1  in
                      let t2 =
                        let uu____11918 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____11918 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12029)::uu____12030 ->
                    (log cfg
                       (fun uu____12043  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12044)::uu____12045 ->
                    (log cfg
                       (fun uu____12056  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12057,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12058;
                                   FStar_Syntax_Syntax.vars = uu____12059;_},uu____12060,uu____12061))::uu____12062
                    ->
                    (log cfg
                       (fun uu____12071  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12072)::uu____12073 ->
                    (log cfg
                       (fun uu____12084  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12085 ->
                    (log cfg
                       (fun uu____12088  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____12092  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12109 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____12109
                         | FStar_Util.Inr c ->
                             let uu____12117 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____12117
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____12130 =
                               let uu____12131 =
                                 let uu____12158 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12158, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12131
                                in
                             mk uu____12130 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____12177 ->
                           let uu____12178 =
                             let uu____12179 =
                               let uu____12180 =
                                 let uu____12207 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12207, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12180
                                in
                             mk uu____12179 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____12178))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               let cfg1 =
                 if (cfg.steps).iota
                 then
                   let uu___153_12284 = cfg  in
                   {
                     steps =
                       (let uu___154_12287 = cfg.steps  in
                        {
                          beta = (uu___154_12287.beta);
                          iota = (uu___154_12287.iota);
                          zeta = (uu___154_12287.zeta);
                          weak = true;
                          hnf = (uu___154_12287.hnf);
                          primops = (uu___154_12287.primops);
                          no_delta_steps = (uu___154_12287.no_delta_steps);
                          unfold_until = (uu___154_12287.unfold_until);
                          unfold_only = (uu___154_12287.unfold_only);
                          unfold_attr = (uu___154_12287.unfold_attr);
                          unfold_tac = (uu___154_12287.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___154_12287.pure_subterms_within_computations);
                          simplify = (uu___154_12287.simplify);
                          erase_universes = (uu___154_12287.erase_universes);
                          allow_unbound_universes =
                            (uu___154_12287.allow_unbound_universes);
                          reify_ = (uu___154_12287.reify_);
                          compress_uvars = (uu___154_12287.compress_uvars);
                          no_full_norm = (uu___154_12287.no_full_norm);
                          check_no_uvars = (uu___154_12287.check_no_uvars);
                          unmeta = (uu___154_12287.unmeta);
                          unascribe = (uu___154_12287.unascribe)
                        });
                     tcenv = (uu___153_12284.tcenv);
                     debug = (uu___153_12284.debug);
                     delta_level = (uu___153_12284.delta_level);
                     primitive_steps = (uu___153_12284.primitive_steps);
                     strong = (uu___153_12284.strong);
                     memoize_lazy = (uu___153_12284.memoize_lazy);
                     normalize_pure_lets =
                       (uu___153_12284.normalize_pure_lets)
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
                         let uu____12323 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12323 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___155_12343 = cfg  in
                               let uu____12344 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___155_12343.steps);
                                 tcenv = uu____12344;
                                 debug = (uu___155_12343.debug);
                                 delta_level = (uu___155_12343.delta_level);
                                 primitive_steps =
                                   (uu___155_12343.primitive_steps);
                                 strong = (uu___155_12343.strong);
                                 memoize_lazy = (uu___155_12343.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___155_12343.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____12349 =
                                 let uu____12350 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____12350  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12349
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___156_12353 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___156_12353.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___156_12353.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___156_12353.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___156_12353.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12354 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12354
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12365,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12366;
                               FStar_Syntax_Syntax.lbunivs = uu____12367;
                               FStar_Syntax_Syntax.lbtyp = uu____12368;
                               FStar_Syntax_Syntax.lbeff = uu____12369;
                               FStar_Syntax_Syntax.lbdef = uu____12370;
                               FStar_Syntax_Syntax.lbattrs = uu____12371;
                               FStar_Syntax_Syntax.lbpos = uu____12372;_}::uu____12373),uu____12374)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____12414 =
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
               if uu____12414
               then
                 let binder =
                   let uu____12416 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____12416  in
                 let env1 =
                   let uu____12426 =
                     let uu____12433 =
                       let uu____12434 =
                         let uu____12465 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12465,
                           false)
                          in
                       Clos uu____12434  in
                     ((FStar_Pervasives_Native.Some binder), uu____12433)  in
                   uu____12426 :: env  in
                 (log cfg
                    (fun uu____12558  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____12562  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12563 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____12563))
                 else
                   (let uu____12565 =
                      let uu____12570 =
                        let uu____12571 =
                          let uu____12572 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____12572
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____12571]  in
                      FStar_Syntax_Subst.open_term uu____12570 body  in
                    match uu____12565 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____12581  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____12589 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____12589  in
                            FStar_Util.Inl
                              (let uu___157_12599 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___157_12599.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___157_12599.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____12602  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___158_12604 = lb  in
                             let uu____12605 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___158_12604.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___158_12604.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____12605;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___158_12604.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___158_12604.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12640  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___159_12663 = cfg  in
                             {
                               steps = (uu___159_12663.steps);
                               tcenv = (uu___159_12663.tcenv);
                               debug = (uu___159_12663.debug);
                               delta_level = (uu___159_12663.delta_level);
                               primitive_steps =
                                 (uu___159_12663.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___159_12663.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___159_12663.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____12666  ->
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
               let uu____12683 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____12683 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____12719 =
                               let uu___160_12720 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___160_12720.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___160_12720.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____12719  in
                           let uu____12721 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____12721 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____12747 =
                                   FStar_List.map (fun uu____12763  -> dummy)
                                     lbs1
                                    in
                                 let uu____12764 =
                                   let uu____12773 =
                                     FStar_List.map
                                       (fun uu____12793  -> dummy) xs1
                                      in
                                   FStar_List.append uu____12773 env  in
                                 FStar_List.append uu____12747 uu____12764
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12817 =
                                       let uu___161_12818 = rc  in
                                       let uu____12819 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___161_12818.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12819;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___161_12818.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____12817
                                 | uu____12826 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___162_12830 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___162_12830.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___162_12830.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___162_12830.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___162_12830.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____12840 =
                        FStar_List.map (fun uu____12856  -> dummy) lbs2  in
                      FStar_List.append uu____12840 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____12864 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____12864 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___163_12880 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___163_12880.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___163_12880.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____12907 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____12907
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____12926 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13002  ->
                        match uu____13002 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___164_13123 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___164_13123.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___164_13123.FStar_Syntax_Syntax.sort)
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
               (match uu____12926 with
                | (rec_env,memos,uu____13336) ->
                    let uu____13389 =
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
                             let uu____13700 =
                               let uu____13707 =
                                 let uu____13708 =
                                   let uu____13739 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____13739, false)
                                    in
                                 Clos uu____13708  in
                               (FStar_Pervasives_Native.None, uu____13707)
                                in
                             uu____13700 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____13849  ->
                     let uu____13850 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____13850);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____13872 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____13874::uu____13875 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____13880) ->
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
                             | uu____13903 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____13917 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____13917
                              | uu____13928 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____13932 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____13958 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____13976 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____13993 =
                        let uu____13994 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____13995 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____13994 uu____13995
                         in
                      failwith uu____13993
                    else rebuild cfg env stack t2
                | uu____13997 -> norm cfg env stack t2))

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
                let uu____14007 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____14007  in
              let uu____14008 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14008 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____14021  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____14032  ->
                        let uu____14033 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14034 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____14033 uu____14034);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____14039 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____14039 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____14048))::stack1 ->
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
                      | uu____14103 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____14106 ->
                          let uu____14109 =
                            let uu____14110 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14110
                             in
                          failwith uu____14109
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
                  let uu___165_14134 = cfg  in
                  let uu____14135 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____14135;
                    tcenv = (uu___165_14134.tcenv);
                    debug = (uu___165_14134.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___165_14134.primitive_steps);
                    strong = (uu___165_14134.strong);
                    memoize_lazy = (uu___165_14134.memoize_lazy);
                    normalize_pure_lets =
                      (uu___165_14134.normalize_pure_lets)
                  }
                else
                  (let uu___166_14137 = cfg  in
                   {
                     steps =
                       (let uu___167_14140 = cfg.steps  in
                        {
                          beta = (uu___167_14140.beta);
                          iota = (uu___167_14140.iota);
                          zeta = false;
                          weak = (uu___167_14140.weak);
                          hnf = (uu___167_14140.hnf);
                          primops = (uu___167_14140.primops);
                          no_delta_steps = (uu___167_14140.no_delta_steps);
                          unfold_until = (uu___167_14140.unfold_until);
                          unfold_only = (uu___167_14140.unfold_only);
                          unfold_attr = (uu___167_14140.unfold_attr);
                          unfold_tac = (uu___167_14140.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___167_14140.pure_subterms_within_computations);
                          simplify = (uu___167_14140.simplify);
                          erase_universes = (uu___167_14140.erase_universes);
                          allow_unbound_universes =
                            (uu___167_14140.allow_unbound_universes);
                          reify_ = (uu___167_14140.reify_);
                          compress_uvars = (uu___167_14140.compress_uvars);
                          no_full_norm = (uu___167_14140.no_full_norm);
                          check_no_uvars = (uu___167_14140.check_no_uvars);
                          unmeta = (uu___167_14140.unmeta);
                          unascribe = (uu___167_14140.unascribe)
                        });
                     tcenv = (uu___166_14137.tcenv);
                     debug = (uu___166_14137.debug);
                     delta_level = (uu___166_14137.delta_level);
                     primitive_steps = (uu___166_14137.primitive_steps);
                     strong = (uu___166_14137.strong);
                     memoize_lazy = (uu___166_14137.memoize_lazy);
                     normalize_pure_lets =
                       (uu___166_14137.normalize_pure_lets)
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
                  (fun uu____14170  ->
                     let uu____14171 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____14172 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____14171
                       uu____14172);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____14174 =
                   let uu____14175 = FStar_Syntax_Subst.compress head3  in
                   uu____14175.FStar_Syntax_Syntax.n  in
                 match uu____14174 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____14193 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14193
                        in
                     let uu____14194 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____14194 with
                      | (uu____14195,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____14201 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____14209 =
                                   let uu____14210 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____14210.FStar_Syntax_Syntax.n  in
                                 match uu____14209 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____14216,uu____14217))
                                     ->
                                     let uu____14226 =
                                       let uu____14227 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____14227.FStar_Syntax_Syntax.n  in
                                     (match uu____14226 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____14233,msrc,uu____14235))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____14244 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14244
                                      | uu____14245 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____14246 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____14247 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____14247 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___168_14252 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___168_14252.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___168_14252.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___168_14252.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___168_14252.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___168_14252.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____14253 = FStar_List.tl stack  in
                                    let uu____14254 =
                                      let uu____14255 =
                                        let uu____14258 =
                                          let uu____14259 =
                                            let uu____14272 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____14272)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____14259
                                           in
                                        FStar_Syntax_Syntax.mk uu____14258
                                         in
                                      uu____14255
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____14253 uu____14254
                                | FStar_Pervasives_Native.None  ->
                                    let uu____14288 =
                                      let uu____14289 = is_return body  in
                                      match uu____14289 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____14293;
                                            FStar_Syntax_Syntax.vars =
                                              uu____14294;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____14299 -> false  in
                                    if uu____14288
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
                                         let uu____14322 =
                                           let uu____14325 =
                                             let uu____14326 =
                                               let uu____14343 =
                                                 let uu____14346 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____14346]  in
                                               (uu____14343, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____14326
                                              in
                                           FStar_Syntax_Syntax.mk uu____14325
                                            in
                                         uu____14322
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____14362 =
                                           let uu____14363 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____14363.FStar_Syntax_Syntax.n
                                            in
                                         match uu____14362 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____14369::uu____14370::[])
                                             ->
                                             let uu____14377 =
                                               let uu____14380 =
                                                 let uu____14381 =
                                                   let uu____14388 =
                                                     let uu____14391 =
                                                       let uu____14392 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____14392
                                                        in
                                                     let uu____14393 =
                                                       let uu____14396 =
                                                         let uu____14397 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____14397
                                                          in
                                                       [uu____14396]  in
                                                     uu____14391 ::
                                                       uu____14393
                                                      in
                                                   (bind1, uu____14388)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____14381
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____14380
                                                in
                                             uu____14377
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____14405 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____14411 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____14411
                                         then
                                           let uu____14414 =
                                             let uu____14415 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____14415
                                              in
                                           let uu____14416 =
                                             let uu____14419 =
                                               let uu____14420 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____14420
                                                in
                                             [uu____14419]  in
                                           uu____14414 :: uu____14416
                                         else []  in
                                       let reified =
                                         let uu____14425 =
                                           let uu____14428 =
                                             let uu____14429 =
                                               let uu____14444 =
                                                 let uu____14447 =
                                                   let uu____14450 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____14451 =
                                                     let uu____14454 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____14454]  in
                                                   uu____14450 :: uu____14451
                                                    in
                                                 let uu____14455 =
                                                   let uu____14458 =
                                                     let uu____14461 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____14462 =
                                                       let uu____14465 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____14466 =
                                                         let uu____14469 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____14470 =
                                                           let uu____14473 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____14473]  in
                                                         uu____14469 ::
                                                           uu____14470
                                                          in
                                                       uu____14465 ::
                                                         uu____14466
                                                        in
                                                     uu____14461 ::
                                                       uu____14462
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____14458
                                                    in
                                                 FStar_List.append
                                                   uu____14447 uu____14455
                                                  in
                                               (bind_inst, uu____14444)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____14429
                                              in
                                           FStar_Syntax_Syntax.mk uu____14428
                                            in
                                         uu____14425
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____14485  ->
                                            let uu____14486 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____14487 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____14486 uu____14487);
                                       (let uu____14488 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____14488 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____14512 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14512
                        in
                     let uu____14513 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____14513 with
                      | (uu____14514,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____14549 =
                                  let uu____14550 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____14550.FStar_Syntax_Syntax.n  in
                                match uu____14549 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____14556) -> t2
                                | uu____14561 -> head4  in
                              let uu____14562 =
                                let uu____14563 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____14563.FStar_Syntax_Syntax.n  in
                              match uu____14562 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____14569 -> FStar_Pervasives_Native.None
                               in
                            let uu____14570 = maybe_extract_fv head4  in
                            match uu____14570 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____14580 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____14580
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____14585 = maybe_extract_fv head5
                                     in
                                  match uu____14585 with
                                  | FStar_Pervasives_Native.Some uu____14590
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____14591 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____14596 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____14611 =
                              match uu____14611 with
                              | (e,q) ->
                                  let uu____14618 =
                                    let uu____14619 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14619.FStar_Syntax_Syntax.n  in
                                  (match uu____14618 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____14634 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____14634
                                   | uu____14635 -> false)
                               in
                            let uu____14636 =
                              let uu____14637 =
                                let uu____14644 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____14644 :: args  in
                              FStar_Util.for_some is_arg_impure uu____14637
                               in
                            if uu____14636
                            then
                              let uu____14649 =
                                let uu____14650 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompability between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____14650
                                 in
                              failwith uu____14649
                            else ());
                           (let uu____14652 = maybe_unfold_action head_app
                               in
                            match uu____14652 with
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
                                   (fun uu____14693  ->
                                      let uu____14694 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____14695 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____14694 uu____14695);
                                 (let uu____14696 = FStar_List.tl stack  in
                                  norm cfg env uu____14696 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____14698) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____14722 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____14722  in
                     (log cfg
                        (fun uu____14726  ->
                           let uu____14727 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____14727);
                      (let uu____14728 = FStar_List.tl stack  in
                       norm cfg env uu____14728 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____14849  ->
                               match uu____14849 with
                               | (pat,wopt,tm) ->
                                   let uu____14897 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____14897)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____14929 = FStar_List.tl stack  in
                     norm cfg env uu____14929 tm
                 | uu____14930 -> fallback ())

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
              (fun uu____14944  ->
                 let uu____14945 = FStar_Ident.string_of_lid msrc  in
                 let uu____14946 = FStar_Ident.string_of_lid mtgt  in
                 let uu____14947 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____14945
                   uu____14946 uu____14947);
            (let uu____14948 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____14948
             then
               let ed =
                 let uu____14950 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____14950  in
               let uu____14951 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____14951 with
               | (uu____14952,return_repr) ->
                   let return_inst =
                     let uu____14961 =
                       let uu____14962 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____14962.FStar_Syntax_Syntax.n  in
                     match uu____14961 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____14968::[]) ->
                         let uu____14975 =
                           let uu____14978 =
                             let uu____14979 =
                               let uu____14986 =
                                 let uu____14989 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____14989]  in
                               (return_tm, uu____14986)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____14979  in
                           FStar_Syntax_Syntax.mk uu____14978  in
                         uu____14975 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____14997 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____15000 =
                     let uu____15003 =
                       let uu____15004 =
                         let uu____15019 =
                           let uu____15022 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____15023 =
                             let uu____15026 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____15026]  in
                           uu____15022 :: uu____15023  in
                         (return_inst, uu____15019)  in
                       FStar_Syntax_Syntax.Tm_app uu____15004  in
                     FStar_Syntax_Syntax.mk uu____15003  in
                   uu____15000 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____15035 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____15035 with
                | FStar_Pervasives_Native.None  ->
                    let uu____15038 =
                      let uu____15039 = FStar_Ident.text_of_lid msrc  in
                      let uu____15040 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____15039 uu____15040
                       in
                    failwith uu____15038
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15041;
                      FStar_TypeChecker_Env.mtarget = uu____15042;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15043;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____15058 =
                      let uu____15059 = FStar_Ident.text_of_lid msrc  in
                      let uu____15060 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____15059 uu____15060
                       in
                    failwith uu____15058
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15061;
                      FStar_TypeChecker_Env.mtarget = uu____15062;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15063;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____15087 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____15088 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____15087 t FStar_Syntax_Syntax.tun uu____15088))

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
                (fun uu____15144  ->
                   match uu____15144 with
                   | (a,imp) ->
                       let uu____15155 = norm cfg env [] a  in
                       (uu____15155, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        match comp.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,uopt) ->
            let uu___169_15169 = comp  in
            let uu____15170 =
              let uu____15171 =
                let uu____15180 = norm cfg env [] t  in
                let uu____15181 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____15180, uu____15181)  in
              FStar_Syntax_Syntax.Total uu____15171  in
            {
              FStar_Syntax_Syntax.n = uu____15170;
              FStar_Syntax_Syntax.pos =
                (uu___169_15169.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___169_15169.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
            let uu___170_15196 = comp  in
            let uu____15197 =
              let uu____15198 =
                let uu____15207 = norm cfg env [] t  in
                let uu____15208 =
                  FStar_Option.map (norm_universe cfg env) uopt  in
                (uu____15207, uu____15208)  in
              FStar_Syntax_Syntax.GTotal uu____15198  in
            {
              FStar_Syntax_Syntax.n = uu____15197;
              FStar_Syntax_Syntax.pos =
                (uu___170_15196.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___170_15196.FStar_Syntax_Syntax.vars)
            }
        | FStar_Syntax_Syntax.Comp ct ->
            let norm_args args =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____15260  ->
                      match uu____15260 with
                      | (a,i) ->
                          let uu____15271 = norm cfg env [] a  in
                          (uu____15271, i)))
               in
            let flags1 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___90_15282  ->
                      match uu___90_15282 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____15286 = norm cfg env [] t  in
                          FStar_Syntax_Syntax.DECREASES uu____15286
                      | f -> f))
               in
            let uu___171_15290 = comp  in
            let uu____15291 =
              let uu____15292 =
                let uu___172_15293 = ct  in
                let uu____15294 =
                  FStar_List.map (norm_universe cfg env)
                    ct.FStar_Syntax_Syntax.comp_univs
                   in
                let uu____15295 =
                  norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
                let uu____15298 =
                  norm_args ct.FStar_Syntax_Syntax.effect_args  in
                {
                  FStar_Syntax_Syntax.comp_univs = uu____15294;
                  FStar_Syntax_Syntax.effect_name =
                    (uu___172_15293.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ = uu____15295;
                  FStar_Syntax_Syntax.effect_args = uu____15298;
                  FStar_Syntax_Syntax.flags = flags1
                }  in
              FStar_Syntax_Syntax.Comp uu____15292  in
            {
              FStar_Syntax_Syntax.n = uu____15291;
              FStar_Syntax_Syntax.pos =
                (uu___171_15290.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___171_15290.FStar_Syntax_Syntax.vars)
            }

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____15309  ->
        match uu____15309 with
        | (x,imp) ->
            let uu____15312 =
              let uu___173_15313 = x  in
              let uu____15314 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___173_15313.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___173_15313.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15314
              }  in
            (uu____15312, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15320 =
          FStar_List.fold_left
            (fun uu____15338  ->
               fun b  ->
                 match uu____15338 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____15320 with | (nbs,uu____15378) -> FStar_List.rev nbs

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
            let uu____15394 =
              let uu___174_15395 = rc  in
              let uu____15396 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___174_15395.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15396;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___174_15395.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____15394
        | uu____15403 -> lopt

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
            (let uu____15424 = FStar_Syntax_Print.term_to_string tm  in
             let uu____15425 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____15424
               uu____15425)
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
          let uu____15445 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____15445
          then tm1
          else
            (let w t =
               let uu___175_15457 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___175_15457.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___175_15457.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____15466 =
                 let uu____15467 = FStar_Syntax_Util.unmeta t  in
                 uu____15467.FStar_Syntax_Syntax.n  in
               match uu____15466 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____15474 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____15519)::args1,(bv,uu____15522)::bs1) ->
                   let uu____15556 =
                     let uu____15557 = FStar_Syntax_Subst.compress t  in
                     uu____15557.FStar_Syntax_Syntax.n  in
                   (match uu____15556 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____15561 -> false)
               | ([],[]) -> true
               | (uu____15582,uu____15583) -> false  in
             let is_applied bs t =
               let uu____15619 = FStar_Syntax_Util.head_and_args' t  in
               match uu____15619 with
               | (hd1,args) ->
                   let uu____15652 =
                     let uu____15653 = FStar_Syntax_Subst.compress hd1  in
                     uu____15653.FStar_Syntax_Syntax.n  in
                   (match uu____15652 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____15659 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____15671 = FStar_Syntax_Util.is_squash t  in
               match uu____15671 with
               | FStar_Pervasives_Native.Some (uu____15682,t') ->
                   is_applied bs t'
               | uu____15694 ->
                   let uu____15703 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____15703 with
                    | FStar_Pervasives_Native.Some (uu____15714,t') ->
                        is_applied bs t'
                    | uu____15726 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____15743 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15743 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____15750)::(q,uu____15752)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____15787 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____15787 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____15792 =
                          let uu____15793 = FStar_Syntax_Subst.compress p  in
                          uu____15793.FStar_Syntax_Syntax.n  in
                        (match uu____15792 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15799 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____15799
                         | uu____15800 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____15803)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____15828 =
                          let uu____15829 = FStar_Syntax_Subst.compress p1
                             in
                          uu____15829.FStar_Syntax_Syntax.n  in
                        (match uu____15828 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15835 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____15835
                         | uu____15836 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____15840 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____15840 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____15845 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____15845 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____15852 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____15852
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____15855)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____15880 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____15880 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____15887 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____15887
                              | uu____15888 -> FStar_Pervasives_Native.None)
                         | uu____15891 -> FStar_Pervasives_Native.None)
                    | uu____15894 -> FStar_Pervasives_Native.None)
               | uu____15897 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____15908 =
                 let uu____15909 = FStar_Syntax_Subst.compress phi  in
                 uu____15909.FStar_Syntax_Syntax.n  in
               match uu____15908 with
               | FStar_Syntax_Syntax.Tm_match (uu____15914,br::brs) ->
                   let uu____15981 = br  in
                   (match uu____15981 with
                    | (uu____15998,uu____15999,e) ->
                        let r =
                          let uu____16020 = simp_t e  in
                          match uu____16020 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____16026 =
                                FStar_List.for_all
                                  (fun uu____16044  ->
                                     match uu____16044 with
                                     | (uu____16057,uu____16058,e') ->
                                         let uu____16072 = simp_t e'  in
                                         uu____16072 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____16026
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____16080 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____16085 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____16085
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____16106 =
                 match uu____16106 with
                 | (t1,q) ->
                     let uu____16119 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____16119 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____16147 -> (t1, q))
                  in
               let uu____16156 = FStar_Syntax_Util.head_and_args t  in
               match uu____16156 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____16218 =
                 let uu____16219 = FStar_Syntax_Util.unmeta ty  in
                 uu____16219.FStar_Syntax_Syntax.n  in
               match uu____16218 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____16223) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____16228,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____16248 -> false  in
             let simplify1 arg =
               let uu____16271 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____16271, arg)  in
             let uu____16280 = is_quantified_const tm1  in
             match uu____16280 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____16284 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____16284
             | FStar_Pervasives_Native.None  ->
                 let uu____16285 =
                   let uu____16286 = FStar_Syntax_Subst.compress tm1  in
                   uu____16286.FStar_Syntax_Syntax.n  in
                 (match uu____16285 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____16290;
                              FStar_Syntax_Syntax.vars = uu____16291;_},uu____16292);
                         FStar_Syntax_Syntax.pos = uu____16293;
                         FStar_Syntax_Syntax.vars = uu____16294;_},args)
                      ->
                      let uu____16320 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____16320
                      then
                        let uu____16321 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____16321 with
                         | (FStar_Pervasives_Native.Some (true ),uu____16368)::
                             (uu____16369,(arg,uu____16371))::[] ->
                             maybe_auto_squash arg
                         | (uu____16420,(arg,uu____16422))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____16423)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____16472)::uu____16473::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16524::(FStar_Pervasives_Native.Some (false
                                         ),uu____16525)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____16576 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16590 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____16590
                         then
                           let uu____16591 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____16591 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____16638)::uu____16639::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16690::(FStar_Pervasives_Native.Some (true
                                           ),uu____16691)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____16742)::(uu____16743,(arg,uu____16745))::[]
                               -> maybe_auto_squash arg
                           | (uu____16794,(arg,uu____16796))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____16797)::[]
                               -> maybe_auto_squash arg
                           | uu____16846 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____16860 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____16860
                            then
                              let uu____16861 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____16861 with
                              | uu____16908::(FStar_Pervasives_Native.Some
                                              (true ),uu____16909)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____16960)::uu____16961::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____17012)::(uu____17013,(arg,uu____17015))::[]
                                  -> maybe_auto_squash arg
                              | (uu____17064,(p,uu____17066))::(uu____17067,
                                                                (q,uu____17069))::[]
                                  ->
                                  let uu____17116 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____17116
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____17118 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____17132 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____17132
                               then
                                 let uu____17133 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____17133 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17180)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17181)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17232)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17233)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17284)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17285)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17336)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17337)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____17388,(arg,uu____17390))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____17391)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17440)::(uu____17441,(arg,uu____17443))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____17492,(arg,uu____17494))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____17495)::[]
                                     ->
                                     let uu____17544 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17544
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17545)::(uu____17546,(arg,uu____17548))::[]
                                     ->
                                     let uu____17597 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17597
                                 | (uu____17598,(p,uu____17600))::(uu____17601,
                                                                   (q,uu____17603))::[]
                                     ->
                                     let uu____17650 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____17650
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17652 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17666 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____17666
                                  then
                                    let uu____17667 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____17667 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____17714)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____17745)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17776 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17790 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____17790
                                     then
                                       match args with
                                       | (t,uu____17792)::[] ->
                                           let uu____17809 =
                                             let uu____17810 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17810.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17809 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17813::[],body,uu____17815)
                                                ->
                                                let uu____17842 = simp_t body
                                                   in
                                                (match uu____17842 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____17845 -> tm1)
                                            | uu____17848 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____17850))::(t,uu____17852)::[]
                                           ->
                                           let uu____17891 =
                                             let uu____17892 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17892.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17891 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17895::[],body,uu____17897)
                                                ->
                                                let uu____17924 = simp_t body
                                                   in
                                                (match uu____17924 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____17927 -> tm1)
                                            | uu____17930 -> tm1)
                                       | uu____17931 -> tm1
                                     else
                                       (let uu____17941 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____17941
                                        then
                                          match args with
                                          | (t,uu____17943)::[] ->
                                              let uu____17960 =
                                                let uu____17961 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17961.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17960 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17964::[],body,uu____17966)
                                                   ->
                                                   let uu____17993 =
                                                     simp_t body  in
                                                   (match uu____17993 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____17996 -> tm1)
                                               | uu____17999 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____18001))::(t,uu____18003)::[]
                                              ->
                                              let uu____18042 =
                                                let uu____18043 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18043.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18042 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18046::[],body,uu____18048)
                                                   ->
                                                   let uu____18075 =
                                                     simp_t body  in
                                                   (match uu____18075 with
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
                                                    | uu____18078 -> tm1)
                                               | uu____18081 -> tm1)
                                          | uu____18082 -> tm1
                                        else
                                          (let uu____18092 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____18092
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18093;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18094;_},uu____18095)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18112;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18113;_},uu____18114)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____18131 -> tm1
                                           else
                                             (let uu____18141 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____18141 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____18161 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____18171;
                         FStar_Syntax_Syntax.vars = uu____18172;_},args)
                      ->
                      let uu____18194 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18194
                      then
                        let uu____18195 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18195 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18242)::
                             (uu____18243,(arg,uu____18245))::[] ->
                             maybe_auto_squash arg
                         | (uu____18294,(arg,uu____18296))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18297)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18346)::uu____18347::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18398::(FStar_Pervasives_Native.Some (false
                                         ),uu____18399)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18450 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18464 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18464
                         then
                           let uu____18465 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18465 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18512)::uu____18513::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18564::(FStar_Pervasives_Native.Some (true
                                           ),uu____18565)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18616)::(uu____18617,(arg,uu____18619))::[]
                               -> maybe_auto_squash arg
                           | (uu____18668,(arg,uu____18670))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18671)::[]
                               -> maybe_auto_squash arg
                           | uu____18720 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18734 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18734
                            then
                              let uu____18735 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18735 with
                              | uu____18782::(FStar_Pervasives_Native.Some
                                              (true ),uu____18783)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18834)::uu____18835::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18886)::(uu____18887,(arg,uu____18889))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18938,(p,uu____18940))::(uu____18941,
                                                                (q,uu____18943))::[]
                                  ->
                                  let uu____18990 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____18990
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18992 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19006 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19006
                               then
                                 let uu____19007 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19007 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19054)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19055)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19106)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19107)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19158)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19159)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19210)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19211)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19262,(arg,uu____19264))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19265)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19314)::(uu____19315,(arg,uu____19317))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19366,(arg,uu____19368))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19369)::[]
                                     ->
                                     let uu____19418 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19418
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19419)::(uu____19420,(arg,uu____19422))::[]
                                     ->
                                     let uu____19471 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19471
                                 | (uu____19472,(p,uu____19474))::(uu____19475,
                                                                   (q,uu____19477))::[]
                                     ->
                                     let uu____19524 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19524
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19526 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19540 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19540
                                  then
                                    let uu____19541 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19541 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19588)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19619)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19650 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19664 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19664
                                     then
                                       match args with
                                       | (t,uu____19666)::[] ->
                                           let uu____19683 =
                                             let uu____19684 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19684.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19683 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19687::[],body,uu____19689)
                                                ->
                                                let uu____19716 = simp_t body
                                                   in
                                                (match uu____19716 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19719 -> tm1)
                                            | uu____19722 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19724))::(t,uu____19726)::[]
                                           ->
                                           let uu____19765 =
                                             let uu____19766 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19766.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19765 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19769::[],body,uu____19771)
                                                ->
                                                let uu____19798 = simp_t body
                                                   in
                                                (match uu____19798 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19801 -> tm1)
                                            | uu____19804 -> tm1)
                                       | uu____19805 -> tm1
                                     else
                                       (let uu____19815 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____19815
                                        then
                                          match args with
                                          | (t,uu____19817)::[] ->
                                              let uu____19834 =
                                                let uu____19835 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19835.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19834 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19838::[],body,uu____19840)
                                                   ->
                                                   let uu____19867 =
                                                     simp_t body  in
                                                   (match uu____19867 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____19870 -> tm1)
                                               | uu____19873 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____19875))::(t,uu____19877)::[]
                                              ->
                                              let uu____19916 =
                                                let uu____19917 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19917.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19916 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19920::[],body,uu____19922)
                                                   ->
                                                   let uu____19949 =
                                                     simp_t body  in
                                                   (match uu____19949 with
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
                                                    | uu____19952 -> tm1)
                                               | uu____19955 -> tm1)
                                          | uu____19956 -> tm1
                                        else
                                          (let uu____19966 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____19966
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19967;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19968;_},uu____19969)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19986;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19987;_},uu____19988)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20005 -> tm1
                                           else
                                             (let uu____20015 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20015 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20035 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____20050 = simp_t t  in
                      (match uu____20050 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____20053 ->
                      let uu____20076 = is_const_match tm1  in
                      (match uu____20076 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____20079 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____20090  ->
               let uu____20091 = FStar_Syntax_Print.tag_of_term t  in
               let uu____20092 = FStar_Syntax_Print.term_to_string t  in
               let uu____20093 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____20100 =
                 let uu____20101 =
                   let uu____20104 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____20104
                    in
                 stack_to_string uu____20101  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____20091 uu____20092 uu____20093 uu____20100);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____20135 =
                     let uu____20136 =
                       let uu____20137 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____20137  in
                     FStar_Util.string_of_int uu____20136  in
                   let uu____20142 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____20143 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____20135 uu____20142 uu____20143)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____20149,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____20198  ->
                     let uu____20199 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____20199);
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
               let uu____20235 =
                 let uu___176_20236 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___176_20236.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___176_20236.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____20235
           | (Arg (Univ uu____20237,uu____20238,uu____20239))::uu____20240 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____20243,uu____20244))::uu____20245 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____20260,uu____20261),aq,r))::stack1
               when
               let uu____20311 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____20311 ->
               let t2 =
                 let uu____20315 =
                   let uu____20316 =
                     let uu____20317 = closure_as_term cfg env_arg tm  in
                     (uu____20317, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____20316  in
                 uu____20315 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____20323),aq,r))::stack1 ->
               (log cfg
                  (fun uu____20376  ->
                     let uu____20377 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____20377);
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
                  (let uu____20387 = FStar_ST.op_Bang m  in
                   match uu____20387 with
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
                   | FStar_Pervasives_Native.Some (uu____20524,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____20571 =
                 log cfg
                   (fun uu____20575  ->
                      let uu____20576 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____20576);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____20580 =
                 let uu____20581 = FStar_Syntax_Subst.compress t1  in
                 uu____20581.FStar_Syntax_Syntax.n  in
               (match uu____20580 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____20608 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____20608  in
                    (log cfg
                       (fun uu____20612  ->
                          let uu____20613 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____20613);
                     (let uu____20614 = FStar_List.tl stack  in
                      norm cfg env1 uu____20614 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____20615);
                       FStar_Syntax_Syntax.pos = uu____20616;
                       FStar_Syntax_Syntax.vars = uu____20617;_},(e,uu____20619)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____20648 when
                    (cfg.steps).primops ->
                    let uu____20663 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____20663 with
                     | (hd1,args) ->
                         let uu____20700 =
                           let uu____20701 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____20701.FStar_Syntax_Syntax.n  in
                         (match uu____20700 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____20705 = find_prim_step cfg fv  in
                              (match uu____20705 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____20708; arity = uu____20709;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____20711;
                                     requires_binder_substitution =
                                       uu____20712;
                                     interpretation = uu____20713;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____20726 -> fallback " (3)" ())
                          | uu____20729 -> fallback " (4)" ()))
                | uu____20730 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,cfg1,r))::stack1 ->
               (log cfg1
                  (fun uu____20751  ->
                     let uu____20752 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____20752);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____20757 =
                   log cfg1
                     (fun uu____20762  ->
                        let uu____20763 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____20764 =
                          let uu____20765 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____20782  ->
                                    match uu____20782 with
                                    | (p,uu____20792,uu____20793) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____20765
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____20763 uu____20764);
                   (let whnf = (cfg1.steps).weak || (cfg1.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg1.delta_level
                          (FStar_List.filter
                             (fun uu___91_20810  ->
                                match uu___91_20810 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____20811 -> false))
                         in
                      let uu___177_20812 = cfg1  in
                      {
                        steps =
                          (let uu___178_20815 = cfg1.steps  in
                           {
                             beta = (uu___178_20815.beta);
                             iota = (uu___178_20815.iota);
                             zeta = false;
                             weak = (uu___178_20815.weak);
                             hnf = (uu___178_20815.hnf);
                             primops = (uu___178_20815.primops);
                             no_delta_steps = (uu___178_20815.no_delta_steps);
                             unfold_until = (uu___178_20815.unfold_until);
                             unfold_only = (uu___178_20815.unfold_only);
                             unfold_attr = (uu___178_20815.unfold_attr);
                             unfold_tac = (uu___178_20815.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___178_20815.pure_subterms_within_computations);
                             simplify = (uu___178_20815.simplify);
                             erase_universes =
                               (uu___178_20815.erase_universes);
                             allow_unbound_universes =
                               (uu___178_20815.allow_unbound_universes);
                             reify_ = (uu___178_20815.reify_);
                             compress_uvars = (uu___178_20815.compress_uvars);
                             no_full_norm = (uu___178_20815.no_full_norm);
                             check_no_uvars = (uu___178_20815.check_no_uvars);
                             unmeta = (uu___178_20815.unmeta);
                             unascribe = (uu___178_20815.unascribe)
                           });
                        tcenv = (uu___177_20812.tcenv);
                        debug = (uu___177_20812.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___177_20812.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___177_20812.memoize_lazy);
                        normalize_pure_lets =
                          (uu___177_20812.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____20847 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____20868 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____20928  ->
                                    fun uu____20929  ->
                                      match (uu____20928, uu____20929) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____21020 = norm_pat env3 p1
                                             in
                                          (match uu____21020 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____20868 with
                           | (pats1,env3) ->
                               ((let uu___179_21102 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___179_21102.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___180_21121 = x  in
                            let uu____21122 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___180_21121.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___180_21121.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21122
                            }  in
                          ((let uu___181_21136 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___181_21136.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___182_21147 = x  in
                            let uu____21148 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___182_21147.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___182_21147.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21148
                            }  in
                          ((let uu___183_21162 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___183_21162.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___184_21178 = x  in
                            let uu____21179 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___184_21178.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___184_21178.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21179
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___185_21186 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___185_21186.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____21196 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____21210 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____21210 with
                                  | (p,wopt,e) ->
                                      let uu____21230 = norm_pat env1 p  in
                                      (match uu____21230 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____21255 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____21255
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____21261 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____21261)
                    in
                 let rec is_cons head1 =
                   let uu____21266 =
                     let uu____21267 = FStar_Syntax_Subst.compress head1  in
                     uu____21267.FStar_Syntax_Syntax.n  in
                   match uu____21266 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____21271) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____21276 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21277;
                         FStar_Syntax_Syntax.fv_delta = uu____21278;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21279;
                         FStar_Syntax_Syntax.fv_delta = uu____21280;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____21281);_}
                       -> true
                   | uu____21288 -> false  in
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
                   let uu____21433 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____21433 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____21520 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____21559 ->
                                 let uu____21560 =
                                   let uu____21561 = is_cons head1  in
                                   Prims.op_Negation uu____21561  in
                                 FStar_Util.Inr uu____21560)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____21586 =
                              let uu____21587 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____21587.FStar_Syntax_Syntax.n  in
                            (match uu____21586 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____21605 ->
                                 let uu____21606 =
                                   let uu____21607 = is_cons head1  in
                                   Prims.op_Negation uu____21607  in
                                 FStar_Util.Inr uu____21606))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____21676)::rest_a,(p1,uu____21679)::rest_p) ->
                       let uu____21723 = matches_pat t2 p1  in
                       (match uu____21723 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____21772 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____21878 = matches_pat scrutinee1 p1  in
                       (match uu____21878 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg1
                               (fun uu____21918  ->
                                  let uu____21919 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____21920 =
                                    let uu____21921 =
                                      FStar_List.map
                                        (fun uu____21931  ->
                                           match uu____21931 with
                                           | (uu____21936,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____21921
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____21919 uu____21920);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____21967  ->
                                       match uu____21967 with
                                       | (bv,t2) ->
                                           let uu____21990 =
                                             let uu____21997 =
                                               let uu____22000 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____22000
                                                in
                                             let uu____22001 =
                                               let uu____22002 =
                                                 let uu____22033 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____22033, false)
                                                  in
                                               Clos uu____22002  in
                                             (uu____21997, uu____22001)  in
                                           uu____21990 :: env2) env1 s
                                 in
                              let uu____22150 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____22150)))
                    in
                 if (cfg1.steps).iota
                 then matches scrutinee branches
                 else norm_and_rebuild_match ())))

let (plugins :
  (primitive_step -> Prims.unit,Prims.unit -> primitive_step Prims.list)
    FStar_Pervasives_Native.tuple2)
  =
  let plugins = FStar_Util.mk_ref []  in
  let register p =
    let uu____22173 =
      let uu____22176 = FStar_ST.op_Bang plugins  in p :: uu____22176  in
    FStar_ST.op_Colon_Equals plugins uu____22173  in
  let retrieve uu____22274 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____22339  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___92_22372  ->
                  match uu___92_22372 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____22376 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____22382 -> d  in
        let uu____22385 = to_fsteps s  in
        let uu____22386 =
          let uu____22387 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____22388 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____22389 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____22390 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____22391 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____22387;
            primop = uu____22388;
            b380 = uu____22389;
            norm_delayed = uu____22390;
            print_normalized = uu____22391
          }  in
        let uu____22392 =
          let uu____22395 =
            let uu____22398 = retrieve_plugins ()  in
            FStar_List.append uu____22398 psteps  in
          add_steps built_in_primitive_steps uu____22395  in
        let uu____22401 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____22403 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____22403)
           in
        {
          steps = uu____22385;
          tcenv = e;
          debug = uu____22386;
          delta_level = d1;
          primitive_steps = uu____22392;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____22401
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
      fun t  -> let uu____22461 = config s e  in norm_comp uu____22461 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____22474 = config [] env  in norm_universe uu____22474 [] u
  
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
        let uu____22492 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____22492  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____22499 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___186_22518 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___186_22518.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___186_22518.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____22525 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____22525
          then
            let ct1 =
              let uu____22527 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____22527 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____22534 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____22534
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___187_22538 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___187_22538.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___187_22538.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___187_22538.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___188_22540 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___188_22540.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___188_22540.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___188_22540.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___188_22540.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___189_22541 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___189_22541.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___189_22541.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____22543 -> c
  
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
        let uu____22555 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____22555  in
      let uu____22562 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____22562
      then
        let uu____22563 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____22563 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____22569  ->
                 let uu____22570 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____22570)
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
            ((let uu____22587 =
                let uu____22592 =
                  let uu____22593 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22593
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22592)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____22587);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____22604 = config [AllowUnboundUniverses] env  in
          norm_comp uu____22604 [] c
        with
        | e ->
            ((let uu____22617 =
                let uu____22622 =
                  let uu____22623 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22623
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22622)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____22617);
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
                   let uu____22660 =
                     let uu____22661 =
                       let uu____22668 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____22668)  in
                     FStar_Syntax_Syntax.Tm_refine uu____22661  in
                   mk uu____22660 t01.FStar_Syntax_Syntax.pos
               | uu____22673 -> t2)
          | uu____22674 -> t2  in
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
        let uu____22714 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____22714 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____22743 ->
                 let uu____22750 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____22750 with
                  | (actuals,uu____22760,uu____22761) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____22775 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____22775 with
                         | (binders,args) ->
                             let uu____22792 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____22792
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
      | uu____22800 ->
          let uu____22801 = FStar_Syntax_Util.head_and_args t  in
          (match uu____22801 with
           | (head1,args) ->
               let uu____22838 =
                 let uu____22839 = FStar_Syntax_Subst.compress head1  in
                 uu____22839.FStar_Syntax_Syntax.n  in
               (match uu____22838 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____22842,thead) ->
                    let uu____22868 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____22868 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____22910 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___194_22918 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___194_22918.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___194_22918.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___194_22918.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___194_22918.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___194_22918.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___194_22918.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___194_22918.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___194_22918.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___194_22918.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___194_22918.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___194_22918.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___194_22918.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___194_22918.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___194_22918.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___194_22918.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___194_22918.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___194_22918.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___194_22918.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___194_22918.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___194_22918.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___194_22918.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___194_22918.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___194_22918.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___194_22918.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___194_22918.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___194_22918.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___194_22918.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___194_22918.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___194_22918.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___194_22918.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___194_22918.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___194_22918.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___194_22918.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____22910 with
                            | (uu____22919,ty,uu____22921) ->
                                eta_expand_with_type env t ty))
                | uu____22922 ->
                    let uu____22923 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___195_22931 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___195_22931.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___195_22931.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___195_22931.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___195_22931.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___195_22931.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___195_22931.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___195_22931.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___195_22931.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___195_22931.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___195_22931.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___195_22931.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___195_22931.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___195_22931.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___195_22931.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___195_22931.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___195_22931.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___195_22931.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___195_22931.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___195_22931.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___195_22931.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___195_22931.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___195_22931.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___195_22931.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___195_22931.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___195_22931.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___195_22931.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___195_22931.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___195_22931.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___195_22931.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___195_22931.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___195_22931.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___195_22931.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___195_22931.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____22923 with
                     | (uu____22932,ty,uu____22934) ->
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
      let uu___196_22991 = x  in
      let uu____22992 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___196_22991.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___196_22991.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____22992
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____22995 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____23020 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____23021 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____23022 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____23023 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____23030 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____23031 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____23032 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___197_23060 = rc  in
          let uu____23061 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____23068 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___197_23060.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____23061;
            FStar_Syntax_Syntax.residual_flags = uu____23068
          }  in
        let uu____23071 =
          let uu____23072 =
            let uu____23089 = elim_delayed_subst_binders bs  in
            let uu____23096 = elim_delayed_subst_term t2  in
            let uu____23097 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____23089, uu____23096, uu____23097)  in
          FStar_Syntax_Syntax.Tm_abs uu____23072  in
        mk1 uu____23071
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____23126 =
          let uu____23127 =
            let uu____23140 = elim_delayed_subst_binders bs  in
            let uu____23147 = elim_delayed_subst_comp c  in
            (uu____23140, uu____23147)  in
          FStar_Syntax_Syntax.Tm_arrow uu____23127  in
        mk1 uu____23126
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____23160 =
          let uu____23161 =
            let uu____23168 = elim_bv bv  in
            let uu____23169 = elim_delayed_subst_term phi  in
            (uu____23168, uu____23169)  in
          FStar_Syntax_Syntax.Tm_refine uu____23161  in
        mk1 uu____23160
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____23192 =
          let uu____23193 =
            let uu____23208 = elim_delayed_subst_term t2  in
            let uu____23209 = elim_delayed_subst_args args  in
            (uu____23208, uu____23209)  in
          FStar_Syntax_Syntax.Tm_app uu____23193  in
        mk1 uu____23192
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___198_23273 = p  in
              let uu____23274 =
                let uu____23275 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____23275  in
              {
                FStar_Syntax_Syntax.v = uu____23274;
                FStar_Syntax_Syntax.p =
                  (uu___198_23273.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___199_23277 = p  in
              let uu____23278 =
                let uu____23279 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____23279  in
              {
                FStar_Syntax_Syntax.v = uu____23278;
                FStar_Syntax_Syntax.p =
                  (uu___199_23277.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___200_23286 = p  in
              let uu____23287 =
                let uu____23288 =
                  let uu____23295 = elim_bv x  in
                  let uu____23296 = elim_delayed_subst_term t0  in
                  (uu____23295, uu____23296)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____23288  in
              {
                FStar_Syntax_Syntax.v = uu____23287;
                FStar_Syntax_Syntax.p =
                  (uu___200_23286.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___201_23315 = p  in
              let uu____23316 =
                let uu____23317 =
                  let uu____23330 =
                    FStar_List.map
                      (fun uu____23353  ->
                         match uu____23353 with
                         | (x,b) ->
                             let uu____23366 = elim_pat x  in
                             (uu____23366, b)) pats
                     in
                  (fv, uu____23330)  in
                FStar_Syntax_Syntax.Pat_cons uu____23317  in
              {
                FStar_Syntax_Syntax.v = uu____23316;
                FStar_Syntax_Syntax.p =
                  (uu___201_23315.FStar_Syntax_Syntax.p)
              }
          | uu____23379 -> p  in
        let elim_branch uu____23401 =
          match uu____23401 with
          | (pat,wopt,t3) ->
              let uu____23427 = elim_pat pat  in
              let uu____23430 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____23433 = elim_delayed_subst_term t3  in
              (uu____23427, uu____23430, uu____23433)
           in
        let uu____23438 =
          let uu____23439 =
            let uu____23462 = elim_delayed_subst_term t2  in
            let uu____23463 = FStar_List.map elim_branch branches  in
            (uu____23462, uu____23463)  in
          FStar_Syntax_Syntax.Tm_match uu____23439  in
        mk1 uu____23438
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____23572 =
          match uu____23572 with
          | (tc,topt) ->
              let uu____23607 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____23617 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____23617
                | FStar_Util.Inr c ->
                    let uu____23619 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____23619
                 in
              let uu____23620 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____23607, uu____23620)
           in
        let uu____23629 =
          let uu____23630 =
            let uu____23657 = elim_delayed_subst_term t2  in
            let uu____23658 = elim_ascription a  in
            (uu____23657, uu____23658, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____23630  in
        mk1 uu____23629
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___202_23703 = lb  in
          let uu____23704 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____23707 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___202_23703.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___202_23703.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____23704;
            FStar_Syntax_Syntax.lbeff =
              (uu___202_23703.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____23707;
            FStar_Syntax_Syntax.lbattrs =
              (uu___202_23703.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___202_23703.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____23710 =
          let uu____23711 =
            let uu____23724 =
              let uu____23731 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____23731)  in
            let uu____23740 = elim_delayed_subst_term t2  in
            (uu____23724, uu____23740)  in
          FStar_Syntax_Syntax.Tm_let uu____23711  in
        mk1 uu____23710
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____23773 =
          let uu____23774 =
            let uu____23791 = elim_delayed_subst_term t2  in
            (uv, uu____23791)  in
          FStar_Syntax_Syntax.Tm_uvar uu____23774  in
        mk1 uu____23773
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____23809 =
          let uu____23810 =
            let uu____23817 = elim_delayed_subst_term tm  in
            (uu____23817, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____23810  in
        mk1 uu____23809
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____23824 =
          let uu____23825 =
            let uu____23832 = elim_delayed_subst_term t2  in
            let uu____23833 = elim_delayed_subst_meta md  in
            (uu____23832, uu____23833)  in
          FStar_Syntax_Syntax.Tm_meta uu____23825  in
        mk1 uu____23824

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_23840  ->
         match uu___93_23840 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____23844 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____23844
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
        let uu____23865 =
          let uu____23866 =
            let uu____23875 = elim_delayed_subst_term t  in
            (uu____23875, uopt)  in
          FStar_Syntax_Syntax.Total uu____23866  in
        mk1 uu____23865
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____23888 =
          let uu____23889 =
            let uu____23898 = elim_delayed_subst_term t  in
            (uu____23898, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____23889  in
        mk1 uu____23888
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___203_23903 = ct  in
          let uu____23904 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____23907 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____23916 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___203_23903.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___203_23903.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____23904;
            FStar_Syntax_Syntax.effect_args = uu____23907;
            FStar_Syntax_Syntax.flags = uu____23916
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_23919  ->
    match uu___94_23919 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____23931 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____23931
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____23964 =
          let uu____23971 = elim_delayed_subst_term t  in (m, uu____23971)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____23964
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____23979 =
          let uu____23988 = elim_delayed_subst_term t  in
          (m1, m2, uu____23988)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____23979
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____24011  ->
         match uu____24011 with
         | (t,q) ->
             let uu____24022 = elim_delayed_subst_term t  in (uu____24022, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____24042  ->
         match uu____24042 with
         | (x,q) ->
             let uu____24053 =
               let uu___204_24054 = x  in
               let uu____24055 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___204_24054.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___204_24054.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____24055
               }  in
             (uu____24053, q)) bs

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
            | (uu____24131,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____24137,FStar_Util.Inl t) ->
                let uu____24143 =
                  let uu____24146 =
                    let uu____24147 =
                      let uu____24160 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____24160)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____24147  in
                  FStar_Syntax_Syntax.mk uu____24146  in
                uu____24143 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____24164 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____24164 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____24192 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____24247 ->
                    let uu____24248 =
                      let uu____24257 =
                        let uu____24258 = FStar_Syntax_Subst.compress t4  in
                        uu____24258.FStar_Syntax_Syntax.n  in
                      (uu____24257, tc)  in
                    (match uu____24248 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____24283) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____24320) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____24359,FStar_Util.Inl uu____24360) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____24383 -> failwith "Impossible")
                 in
              (match uu____24192 with
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
          let uu____24488 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____24488 with
          | (univ_names1,binders1,tc) ->
              let uu____24546 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____24546)
  
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
          let uu____24581 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____24581 with
          | (univ_names1,binders1,tc) ->
              let uu____24641 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____24641)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____24674 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____24674 with
           | (univ_names1,binders1,typ1) ->
               let uu___205_24702 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___205_24702.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___205_24702.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___205_24702.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___205_24702.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___206_24723 = s  in
          let uu____24724 =
            let uu____24725 =
              let uu____24734 = FStar_List.map (elim_uvars env) sigs  in
              (uu____24734, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____24725  in
          {
            FStar_Syntax_Syntax.sigel = uu____24724;
            FStar_Syntax_Syntax.sigrng =
              (uu___206_24723.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___206_24723.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___206_24723.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___206_24723.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____24751 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24751 with
           | (univ_names1,uu____24769,typ1) ->
               let uu___207_24783 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___207_24783.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___207_24783.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___207_24783.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___207_24783.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____24789 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24789 with
           | (univ_names1,uu____24807,typ1) ->
               let uu___208_24821 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___208_24821.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___208_24821.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___208_24821.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___208_24821.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____24855 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____24855 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____24878 =
                            let uu____24879 =
                              let uu____24880 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____24880  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____24879
                             in
                          elim_delayed_subst_term uu____24878  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___209_24883 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___209_24883.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___209_24883.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___209_24883.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___209_24883.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___210_24884 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___210_24884.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___210_24884.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___210_24884.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___210_24884.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___211_24896 = s  in
          let uu____24897 =
            let uu____24898 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____24898  in
          {
            FStar_Syntax_Syntax.sigel = uu____24897;
            FStar_Syntax_Syntax.sigrng =
              (uu___211_24896.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___211_24896.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___211_24896.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___211_24896.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____24902 = elim_uvars_aux_t env us [] t  in
          (match uu____24902 with
           | (us1,uu____24920,t1) ->
               let uu___212_24934 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___212_24934.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___212_24934.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___212_24934.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___212_24934.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24935 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____24937 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____24937 with
           | (univs1,binders,signature) ->
               let uu____24965 =
                 let uu____24974 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____24974 with
                 | (univs_opening,univs2) ->
                     let uu____25001 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____25001)
                  in
               (match uu____24965 with
                | (univs_opening,univs_closing) ->
                    let uu____25018 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____25024 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____25025 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____25024, uu____25025)  in
                    (match uu____25018 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____25047 =
                           match uu____25047 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____25065 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____25065 with
                                | (us1,t1) ->
                                    let uu____25076 =
                                      let uu____25081 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____25088 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____25081, uu____25088)  in
                                    (match uu____25076 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____25101 =
                                           let uu____25106 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____25115 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____25106, uu____25115)  in
                                         (match uu____25101 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____25131 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____25131
                                                 in
                                              let uu____25132 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____25132 with
                                               | (uu____25153,uu____25154,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____25169 =
                                                       let uu____25170 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____25170
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____25169
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____25175 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____25175 with
                           | (uu____25188,uu____25189,t1) -> t1  in
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
                             | uu____25249 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____25266 =
                               let uu____25267 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____25267.FStar_Syntax_Syntax.n  in
                             match uu____25266 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____25326 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____25355 =
                               let uu____25356 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____25356.FStar_Syntax_Syntax.n  in
                             match uu____25355 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____25377) ->
                                 let uu____25398 = destruct_action_body body
                                    in
                                 (match uu____25398 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____25443 ->
                                 let uu____25444 = destruct_action_body t  in
                                 (match uu____25444 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____25493 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____25493 with
                           | (action_univs,t) ->
                               let uu____25502 = destruct_action_typ_templ t
                                  in
                               (match uu____25502 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___213_25543 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___213_25543.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___213_25543.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___214_25545 = ed  in
                           let uu____25546 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____25547 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____25548 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____25549 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____25550 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____25551 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____25552 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____25553 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____25554 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____25555 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____25556 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____25557 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____25558 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____25559 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___214_25545.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___214_25545.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____25546;
                             FStar_Syntax_Syntax.bind_wp = uu____25547;
                             FStar_Syntax_Syntax.if_then_else = uu____25548;
                             FStar_Syntax_Syntax.ite_wp = uu____25549;
                             FStar_Syntax_Syntax.stronger = uu____25550;
                             FStar_Syntax_Syntax.close_wp = uu____25551;
                             FStar_Syntax_Syntax.assert_p = uu____25552;
                             FStar_Syntax_Syntax.assume_p = uu____25553;
                             FStar_Syntax_Syntax.null_wp = uu____25554;
                             FStar_Syntax_Syntax.trivial = uu____25555;
                             FStar_Syntax_Syntax.repr = uu____25556;
                             FStar_Syntax_Syntax.return_repr = uu____25557;
                             FStar_Syntax_Syntax.bind_repr = uu____25558;
                             FStar_Syntax_Syntax.actions = uu____25559;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___214_25545.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___215_25562 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___215_25562.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___215_25562.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___215_25562.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___215_25562.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_25579 =
            match uu___95_25579 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____25606 = elim_uvars_aux_t env us [] t  in
                (match uu____25606 with
                 | (us1,uu____25630,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___216_25649 = sub_eff  in
            let uu____25650 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____25653 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___216_25649.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___216_25649.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____25650;
              FStar_Syntax_Syntax.lift = uu____25653
            }  in
          let uu___217_25656 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___217_25656.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___217_25656.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___217_25656.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___217_25656.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____25666 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____25666 with
           | (univ_names1,binders1,comp1) ->
               let uu___218_25700 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___218_25700.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___218_25700.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___218_25700.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___218_25700.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____25711 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____25712 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  