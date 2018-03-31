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
  fun projectee  -> match projectee with | Beta  -> true | uu____28 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____32 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____36 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____41 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____52 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____56 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____60 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____64 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____68 -> false
  
let (uu___is_NoDeltaSteps : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDeltaSteps  -> true | uu____72 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____77 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____91 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____111 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____129 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Syntax_Syntax.attribute) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____140 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____144 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____148 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____152 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____156 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____160 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____164 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____168 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____172 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____176 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____180 -> false
  
type steps = step Prims.list[@@deriving show]
let cases :
  'Auu____188 'Auu____189 .
    ('Auu____188 -> 'Auu____189) ->
      'Auu____189 ->
        'Auu____188 FStar_Pervasives_Native.option -> 'Auu____189
  =
  fun f  ->
    fun d  ->
      fun uu___77_206  ->
        match uu___77_206 with
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
  unascribe: Prims.bool }[@@deriving show]
let (__proj__Mkfsteps__item__beta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
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
        unascribe = __fname__unascribe;_} -> __fname__beta
  
let (__proj__Mkfsteps__item__iota : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
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
        unascribe = __fname__unascribe;_} -> __fname__iota
  
let (__proj__Mkfsteps__item__zeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
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
        unascribe = __fname__unascribe;_} -> __fname__zeta
  
let (__proj__Mkfsteps__item__weak : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
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
        unascribe = __fname__unascribe;_} -> __fname__weak
  
let (__proj__Mkfsteps__item__hnf : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
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
        unascribe = __fname__unascribe;_} -> __fname__hnf
  
let (__proj__Mkfsteps__item__primops : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
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
        unascribe = __fname__unascribe;_} -> __fname__primops
  
let (__proj__Mkfsteps__item__no_delta_steps : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
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
        unascribe = __fname__unascribe;_} -> __fname__unfold_only
  
let (__proj__Mkfsteps__item__unfold_fully :
  fsteps -> FStar_Ident.lid Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
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
        unascribe = __fname__unascribe;_} -> __fname__unfold_fully
  
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
        unascribe = __fname__unascribe;_} -> __fname__unfold_attr
  
let (__proj__Mkfsteps__item__unfold_tac : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
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
        unascribe = __fname__unascribe;_} -> __fname__simplify
  
let (__proj__Mkfsteps__item__erase_universes : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
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
        unascribe = __fname__unascribe;_} -> __fname__allow_unbound_universes
  
let (__proj__Mkfsteps__item__reify_ : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
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
        unascribe = __fname__unascribe;_} -> __fname__reify_
  
let (__proj__Mkfsteps__item__compress_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
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
        unascribe = __fname__unascribe;_} -> __fname__compress_uvars
  
let (__proj__Mkfsteps__item__no_full_norm : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
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
        unascribe = __fname__unascribe;_} -> __fname__no_full_norm
  
let (__proj__Mkfsteps__item__check_no_uvars : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
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
        unascribe = __fname__unascribe;_} -> __fname__check_no_uvars
  
let (__proj__Mkfsteps__item__unmeta : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
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
        unascribe = __fname__unascribe;_} -> __fname__unmeta
  
let (__proj__Mkfsteps__item__unascribe : fsteps -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta;
        weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops;
        no_delta_steps = __fname__no_delta_steps;
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
    unascribe = false
  } 
let (fstep_add_one : step -> fsteps -> fsteps) =
  fun s  ->
    fun fs  ->
      let add_opt x uu___78_1226 =
        match uu___78_1226 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some [x]
        | FStar_Pervasives_Native.Some xs ->
            FStar_Pervasives_Native.Some (x :: xs)
         in
      match s with
      | Beta  ->
          let uu___96_1246 = fs  in
          {
            beta = true;
            iota = (uu___96_1246.iota);
            zeta = (uu___96_1246.zeta);
            weak = (uu___96_1246.weak);
            hnf = (uu___96_1246.hnf);
            primops = (uu___96_1246.primops);
            no_delta_steps = (uu___96_1246.no_delta_steps);
            unfold_until = (uu___96_1246.unfold_until);
            unfold_only = (uu___96_1246.unfold_only);
            unfold_fully = (uu___96_1246.unfold_fully);
            unfold_attr = (uu___96_1246.unfold_attr);
            unfold_tac = (uu___96_1246.unfold_tac);
            pure_subterms_within_computations =
              (uu___96_1246.pure_subterms_within_computations);
            simplify = (uu___96_1246.simplify);
            erase_universes = (uu___96_1246.erase_universes);
            allow_unbound_universes = (uu___96_1246.allow_unbound_universes);
            reify_ = (uu___96_1246.reify_);
            compress_uvars = (uu___96_1246.compress_uvars);
            no_full_norm = (uu___96_1246.no_full_norm);
            check_no_uvars = (uu___96_1246.check_no_uvars);
            unmeta = (uu___96_1246.unmeta);
            unascribe = (uu___96_1246.unascribe)
          }
      | Iota  ->
          let uu___97_1247 = fs  in
          {
            beta = (uu___97_1247.beta);
            iota = true;
            zeta = (uu___97_1247.zeta);
            weak = (uu___97_1247.weak);
            hnf = (uu___97_1247.hnf);
            primops = (uu___97_1247.primops);
            no_delta_steps = (uu___97_1247.no_delta_steps);
            unfold_until = (uu___97_1247.unfold_until);
            unfold_only = (uu___97_1247.unfold_only);
            unfold_fully = (uu___97_1247.unfold_fully);
            unfold_attr = (uu___97_1247.unfold_attr);
            unfold_tac = (uu___97_1247.unfold_tac);
            pure_subterms_within_computations =
              (uu___97_1247.pure_subterms_within_computations);
            simplify = (uu___97_1247.simplify);
            erase_universes = (uu___97_1247.erase_universes);
            allow_unbound_universes = (uu___97_1247.allow_unbound_universes);
            reify_ = (uu___97_1247.reify_);
            compress_uvars = (uu___97_1247.compress_uvars);
            no_full_norm = (uu___97_1247.no_full_norm);
            check_no_uvars = (uu___97_1247.check_no_uvars);
            unmeta = (uu___97_1247.unmeta);
            unascribe = (uu___97_1247.unascribe)
          }
      | Zeta  ->
          let uu___98_1248 = fs  in
          {
            beta = (uu___98_1248.beta);
            iota = (uu___98_1248.iota);
            zeta = true;
            weak = (uu___98_1248.weak);
            hnf = (uu___98_1248.hnf);
            primops = (uu___98_1248.primops);
            no_delta_steps = (uu___98_1248.no_delta_steps);
            unfold_until = (uu___98_1248.unfold_until);
            unfold_only = (uu___98_1248.unfold_only);
            unfold_fully = (uu___98_1248.unfold_fully);
            unfold_attr = (uu___98_1248.unfold_attr);
            unfold_tac = (uu___98_1248.unfold_tac);
            pure_subterms_within_computations =
              (uu___98_1248.pure_subterms_within_computations);
            simplify = (uu___98_1248.simplify);
            erase_universes = (uu___98_1248.erase_universes);
            allow_unbound_universes = (uu___98_1248.allow_unbound_universes);
            reify_ = (uu___98_1248.reify_);
            compress_uvars = (uu___98_1248.compress_uvars);
            no_full_norm = (uu___98_1248.no_full_norm);
            check_no_uvars = (uu___98_1248.check_no_uvars);
            unmeta = (uu___98_1248.unmeta);
            unascribe = (uu___98_1248.unascribe)
          }
      | Exclude (Beta ) ->
          let uu___99_1249 = fs  in
          {
            beta = false;
            iota = (uu___99_1249.iota);
            zeta = (uu___99_1249.zeta);
            weak = (uu___99_1249.weak);
            hnf = (uu___99_1249.hnf);
            primops = (uu___99_1249.primops);
            no_delta_steps = (uu___99_1249.no_delta_steps);
            unfold_until = (uu___99_1249.unfold_until);
            unfold_only = (uu___99_1249.unfold_only);
            unfold_fully = (uu___99_1249.unfold_fully);
            unfold_attr = (uu___99_1249.unfold_attr);
            unfold_tac = (uu___99_1249.unfold_tac);
            pure_subterms_within_computations =
              (uu___99_1249.pure_subterms_within_computations);
            simplify = (uu___99_1249.simplify);
            erase_universes = (uu___99_1249.erase_universes);
            allow_unbound_universes = (uu___99_1249.allow_unbound_universes);
            reify_ = (uu___99_1249.reify_);
            compress_uvars = (uu___99_1249.compress_uvars);
            no_full_norm = (uu___99_1249.no_full_norm);
            check_no_uvars = (uu___99_1249.check_no_uvars);
            unmeta = (uu___99_1249.unmeta);
            unascribe = (uu___99_1249.unascribe)
          }
      | Exclude (Iota ) ->
          let uu___100_1250 = fs  in
          {
            beta = (uu___100_1250.beta);
            iota = false;
            zeta = (uu___100_1250.zeta);
            weak = (uu___100_1250.weak);
            hnf = (uu___100_1250.hnf);
            primops = (uu___100_1250.primops);
            no_delta_steps = (uu___100_1250.no_delta_steps);
            unfold_until = (uu___100_1250.unfold_until);
            unfold_only = (uu___100_1250.unfold_only);
            unfold_fully = (uu___100_1250.unfold_fully);
            unfold_attr = (uu___100_1250.unfold_attr);
            unfold_tac = (uu___100_1250.unfold_tac);
            pure_subterms_within_computations =
              (uu___100_1250.pure_subterms_within_computations);
            simplify = (uu___100_1250.simplify);
            erase_universes = (uu___100_1250.erase_universes);
            allow_unbound_universes = (uu___100_1250.allow_unbound_universes);
            reify_ = (uu___100_1250.reify_);
            compress_uvars = (uu___100_1250.compress_uvars);
            no_full_norm = (uu___100_1250.no_full_norm);
            check_no_uvars = (uu___100_1250.check_no_uvars);
            unmeta = (uu___100_1250.unmeta);
            unascribe = (uu___100_1250.unascribe)
          }
      | Exclude (Zeta ) ->
          let uu___101_1251 = fs  in
          {
            beta = (uu___101_1251.beta);
            iota = (uu___101_1251.iota);
            zeta = false;
            weak = (uu___101_1251.weak);
            hnf = (uu___101_1251.hnf);
            primops = (uu___101_1251.primops);
            no_delta_steps = (uu___101_1251.no_delta_steps);
            unfold_until = (uu___101_1251.unfold_until);
            unfold_only = (uu___101_1251.unfold_only);
            unfold_fully = (uu___101_1251.unfold_fully);
            unfold_attr = (uu___101_1251.unfold_attr);
            unfold_tac = (uu___101_1251.unfold_tac);
            pure_subterms_within_computations =
              (uu___101_1251.pure_subterms_within_computations);
            simplify = (uu___101_1251.simplify);
            erase_universes = (uu___101_1251.erase_universes);
            allow_unbound_universes = (uu___101_1251.allow_unbound_universes);
            reify_ = (uu___101_1251.reify_);
            compress_uvars = (uu___101_1251.compress_uvars);
            no_full_norm = (uu___101_1251.no_full_norm);
            check_no_uvars = (uu___101_1251.check_no_uvars);
            unmeta = (uu___101_1251.unmeta);
            unascribe = (uu___101_1251.unascribe)
          }
      | Exclude uu____1252 -> failwith "Bad exclude"
      | Weak  ->
          let uu___102_1253 = fs  in
          {
            beta = (uu___102_1253.beta);
            iota = (uu___102_1253.iota);
            zeta = (uu___102_1253.zeta);
            weak = true;
            hnf = (uu___102_1253.hnf);
            primops = (uu___102_1253.primops);
            no_delta_steps = (uu___102_1253.no_delta_steps);
            unfold_until = (uu___102_1253.unfold_until);
            unfold_only = (uu___102_1253.unfold_only);
            unfold_fully = (uu___102_1253.unfold_fully);
            unfold_attr = (uu___102_1253.unfold_attr);
            unfold_tac = (uu___102_1253.unfold_tac);
            pure_subterms_within_computations =
              (uu___102_1253.pure_subterms_within_computations);
            simplify = (uu___102_1253.simplify);
            erase_universes = (uu___102_1253.erase_universes);
            allow_unbound_universes = (uu___102_1253.allow_unbound_universes);
            reify_ = (uu___102_1253.reify_);
            compress_uvars = (uu___102_1253.compress_uvars);
            no_full_norm = (uu___102_1253.no_full_norm);
            check_no_uvars = (uu___102_1253.check_no_uvars);
            unmeta = (uu___102_1253.unmeta);
            unascribe = (uu___102_1253.unascribe)
          }
      | HNF  ->
          let uu___103_1254 = fs  in
          {
            beta = (uu___103_1254.beta);
            iota = (uu___103_1254.iota);
            zeta = (uu___103_1254.zeta);
            weak = (uu___103_1254.weak);
            hnf = true;
            primops = (uu___103_1254.primops);
            no_delta_steps = (uu___103_1254.no_delta_steps);
            unfold_until = (uu___103_1254.unfold_until);
            unfold_only = (uu___103_1254.unfold_only);
            unfold_fully = (uu___103_1254.unfold_fully);
            unfold_attr = (uu___103_1254.unfold_attr);
            unfold_tac = (uu___103_1254.unfold_tac);
            pure_subterms_within_computations =
              (uu___103_1254.pure_subterms_within_computations);
            simplify = (uu___103_1254.simplify);
            erase_universes = (uu___103_1254.erase_universes);
            allow_unbound_universes = (uu___103_1254.allow_unbound_universes);
            reify_ = (uu___103_1254.reify_);
            compress_uvars = (uu___103_1254.compress_uvars);
            no_full_norm = (uu___103_1254.no_full_norm);
            check_no_uvars = (uu___103_1254.check_no_uvars);
            unmeta = (uu___103_1254.unmeta);
            unascribe = (uu___103_1254.unascribe)
          }
      | Primops  ->
          let uu___104_1255 = fs  in
          {
            beta = (uu___104_1255.beta);
            iota = (uu___104_1255.iota);
            zeta = (uu___104_1255.zeta);
            weak = (uu___104_1255.weak);
            hnf = (uu___104_1255.hnf);
            primops = true;
            no_delta_steps = (uu___104_1255.no_delta_steps);
            unfold_until = (uu___104_1255.unfold_until);
            unfold_only = (uu___104_1255.unfold_only);
            unfold_fully = (uu___104_1255.unfold_fully);
            unfold_attr = (uu___104_1255.unfold_attr);
            unfold_tac = (uu___104_1255.unfold_tac);
            pure_subterms_within_computations =
              (uu___104_1255.pure_subterms_within_computations);
            simplify = (uu___104_1255.simplify);
            erase_universes = (uu___104_1255.erase_universes);
            allow_unbound_universes = (uu___104_1255.allow_unbound_universes);
            reify_ = (uu___104_1255.reify_);
            compress_uvars = (uu___104_1255.compress_uvars);
            no_full_norm = (uu___104_1255.no_full_norm);
            check_no_uvars = (uu___104_1255.check_no_uvars);
            unmeta = (uu___104_1255.unmeta);
            unascribe = (uu___104_1255.unascribe)
          }
      | Eager_unfolding  -> fs
      | Inlining  -> fs
      | NoDeltaSteps  ->
          let uu___105_1256 = fs  in
          {
            beta = (uu___105_1256.beta);
            iota = (uu___105_1256.iota);
            zeta = (uu___105_1256.zeta);
            weak = (uu___105_1256.weak);
            hnf = (uu___105_1256.hnf);
            primops = (uu___105_1256.primops);
            no_delta_steps = true;
            unfold_until = (uu___105_1256.unfold_until);
            unfold_only = (uu___105_1256.unfold_only);
            unfold_fully = (uu___105_1256.unfold_fully);
            unfold_attr = (uu___105_1256.unfold_attr);
            unfold_tac = (uu___105_1256.unfold_tac);
            pure_subterms_within_computations =
              (uu___105_1256.pure_subterms_within_computations);
            simplify = (uu___105_1256.simplify);
            erase_universes = (uu___105_1256.erase_universes);
            allow_unbound_universes = (uu___105_1256.allow_unbound_universes);
            reify_ = (uu___105_1256.reify_);
            compress_uvars = (uu___105_1256.compress_uvars);
            no_full_norm = (uu___105_1256.no_full_norm);
            check_no_uvars = (uu___105_1256.check_no_uvars);
            unmeta = (uu___105_1256.unmeta);
            unascribe = (uu___105_1256.unascribe)
          }
      | UnfoldUntil d ->
          let uu___106_1258 = fs  in
          {
            beta = (uu___106_1258.beta);
            iota = (uu___106_1258.iota);
            zeta = (uu___106_1258.zeta);
            weak = (uu___106_1258.weak);
            hnf = (uu___106_1258.hnf);
            primops = (uu___106_1258.primops);
            no_delta_steps = (uu___106_1258.no_delta_steps);
            unfold_until = (FStar_Pervasives_Native.Some d);
            unfold_only = (uu___106_1258.unfold_only);
            unfold_fully = (uu___106_1258.unfold_fully);
            unfold_attr = (uu___106_1258.unfold_attr);
            unfold_tac = (uu___106_1258.unfold_tac);
            pure_subterms_within_computations =
              (uu___106_1258.pure_subterms_within_computations);
            simplify = (uu___106_1258.simplify);
            erase_universes = (uu___106_1258.erase_universes);
            allow_unbound_universes = (uu___106_1258.allow_unbound_universes);
            reify_ = (uu___106_1258.reify_);
            compress_uvars = (uu___106_1258.compress_uvars);
            no_full_norm = (uu___106_1258.no_full_norm);
            check_no_uvars = (uu___106_1258.check_no_uvars);
            unmeta = (uu___106_1258.unmeta);
            unascribe = (uu___106_1258.unascribe)
          }
      | UnfoldOnly lids ->
          let uu___107_1262 = fs  in
          {
            beta = (uu___107_1262.beta);
            iota = (uu___107_1262.iota);
            zeta = (uu___107_1262.zeta);
            weak = (uu___107_1262.weak);
            hnf = (uu___107_1262.hnf);
            primops = (uu___107_1262.primops);
            no_delta_steps = (uu___107_1262.no_delta_steps);
            unfold_until = (uu___107_1262.unfold_until);
            unfold_only = (FStar_Pervasives_Native.Some lids);
            unfold_fully = (uu___107_1262.unfold_fully);
            unfold_attr = (uu___107_1262.unfold_attr);
            unfold_tac = (uu___107_1262.unfold_tac);
            pure_subterms_within_computations =
              (uu___107_1262.pure_subterms_within_computations);
            simplify = (uu___107_1262.simplify);
            erase_universes = (uu___107_1262.erase_universes);
            allow_unbound_universes = (uu___107_1262.allow_unbound_universes);
            reify_ = (uu___107_1262.reify_);
            compress_uvars = (uu___107_1262.compress_uvars);
            no_full_norm = (uu___107_1262.no_full_norm);
            check_no_uvars = (uu___107_1262.check_no_uvars);
            unmeta = (uu___107_1262.unmeta);
            unascribe = (uu___107_1262.unascribe)
          }
      | UnfoldFully lids ->
          let uu___108_1268 = fs  in
          {
            beta = (uu___108_1268.beta);
            iota = (uu___108_1268.iota);
            zeta = (uu___108_1268.zeta);
            weak = (uu___108_1268.weak);
            hnf = (uu___108_1268.hnf);
            primops = (uu___108_1268.primops);
            no_delta_steps = (uu___108_1268.no_delta_steps);
            unfold_until = (uu___108_1268.unfold_until);
            unfold_only = (uu___108_1268.unfold_only);
            unfold_fully = (FStar_Pervasives_Native.Some lids);
            unfold_attr = (uu___108_1268.unfold_attr);
            unfold_tac = (uu___108_1268.unfold_tac);
            pure_subterms_within_computations =
              (uu___108_1268.pure_subterms_within_computations);
            simplify = (uu___108_1268.simplify);
            erase_universes = (uu___108_1268.erase_universes);
            allow_unbound_universes = (uu___108_1268.allow_unbound_universes);
            reify_ = (uu___108_1268.reify_);
            compress_uvars = (uu___108_1268.compress_uvars);
            no_full_norm = (uu___108_1268.no_full_norm);
            check_no_uvars = (uu___108_1268.check_no_uvars);
            unmeta = (uu___108_1268.unmeta);
            unascribe = (uu___108_1268.unascribe)
          }
      | UnfoldAttr attr ->
          let uu___109_1272 = fs  in
          {
            beta = (uu___109_1272.beta);
            iota = (uu___109_1272.iota);
            zeta = (uu___109_1272.zeta);
            weak = (uu___109_1272.weak);
            hnf = (uu___109_1272.hnf);
            primops = (uu___109_1272.primops);
            no_delta_steps = (uu___109_1272.no_delta_steps);
            unfold_until = (uu___109_1272.unfold_until);
            unfold_only = (uu___109_1272.unfold_only);
            unfold_fully = (uu___109_1272.unfold_fully);
            unfold_attr = (add_opt attr fs.unfold_attr);
            unfold_tac = (uu___109_1272.unfold_tac);
            pure_subterms_within_computations =
              (uu___109_1272.pure_subterms_within_computations);
            simplify = (uu___109_1272.simplify);
            erase_universes = (uu___109_1272.erase_universes);
            allow_unbound_universes = (uu___109_1272.allow_unbound_universes);
            reify_ = (uu___109_1272.reify_);
            compress_uvars = (uu___109_1272.compress_uvars);
            no_full_norm = (uu___109_1272.no_full_norm);
            check_no_uvars = (uu___109_1272.check_no_uvars);
            unmeta = (uu___109_1272.unmeta);
            unascribe = (uu___109_1272.unascribe)
          }
      | UnfoldTac  ->
          let uu___110_1273 = fs  in
          {
            beta = (uu___110_1273.beta);
            iota = (uu___110_1273.iota);
            zeta = (uu___110_1273.zeta);
            weak = (uu___110_1273.weak);
            hnf = (uu___110_1273.hnf);
            primops = (uu___110_1273.primops);
            no_delta_steps = (uu___110_1273.no_delta_steps);
            unfold_until = (uu___110_1273.unfold_until);
            unfold_only = (uu___110_1273.unfold_only);
            unfold_fully = (uu___110_1273.unfold_fully);
            unfold_attr = (uu___110_1273.unfold_attr);
            unfold_tac = true;
            pure_subterms_within_computations =
              (uu___110_1273.pure_subterms_within_computations);
            simplify = (uu___110_1273.simplify);
            erase_universes = (uu___110_1273.erase_universes);
            allow_unbound_universes = (uu___110_1273.allow_unbound_universes);
            reify_ = (uu___110_1273.reify_);
            compress_uvars = (uu___110_1273.compress_uvars);
            no_full_norm = (uu___110_1273.no_full_norm);
            check_no_uvars = (uu___110_1273.check_no_uvars);
            unmeta = (uu___110_1273.unmeta);
            unascribe = (uu___110_1273.unascribe)
          }
      | PureSubtermsWithinComputations  ->
          let uu___111_1274 = fs  in
          {
            beta = (uu___111_1274.beta);
            iota = (uu___111_1274.iota);
            zeta = (uu___111_1274.zeta);
            weak = (uu___111_1274.weak);
            hnf = (uu___111_1274.hnf);
            primops = (uu___111_1274.primops);
            no_delta_steps = (uu___111_1274.no_delta_steps);
            unfold_until = (uu___111_1274.unfold_until);
            unfold_only = (uu___111_1274.unfold_only);
            unfold_fully = (uu___111_1274.unfold_fully);
            unfold_attr = (uu___111_1274.unfold_attr);
            unfold_tac = (uu___111_1274.unfold_tac);
            pure_subterms_within_computations = true;
            simplify = (uu___111_1274.simplify);
            erase_universes = (uu___111_1274.erase_universes);
            allow_unbound_universes = (uu___111_1274.allow_unbound_universes);
            reify_ = (uu___111_1274.reify_);
            compress_uvars = (uu___111_1274.compress_uvars);
            no_full_norm = (uu___111_1274.no_full_norm);
            check_no_uvars = (uu___111_1274.check_no_uvars);
            unmeta = (uu___111_1274.unmeta);
            unascribe = (uu___111_1274.unascribe)
          }
      | Simplify  ->
          let uu___112_1275 = fs  in
          {
            beta = (uu___112_1275.beta);
            iota = (uu___112_1275.iota);
            zeta = (uu___112_1275.zeta);
            weak = (uu___112_1275.weak);
            hnf = (uu___112_1275.hnf);
            primops = (uu___112_1275.primops);
            no_delta_steps = (uu___112_1275.no_delta_steps);
            unfold_until = (uu___112_1275.unfold_until);
            unfold_only = (uu___112_1275.unfold_only);
            unfold_fully = (uu___112_1275.unfold_fully);
            unfold_attr = (uu___112_1275.unfold_attr);
            unfold_tac = (uu___112_1275.unfold_tac);
            pure_subterms_within_computations =
              (uu___112_1275.pure_subterms_within_computations);
            simplify = true;
            erase_universes = (uu___112_1275.erase_universes);
            allow_unbound_universes = (uu___112_1275.allow_unbound_universes);
            reify_ = (uu___112_1275.reify_);
            compress_uvars = (uu___112_1275.compress_uvars);
            no_full_norm = (uu___112_1275.no_full_norm);
            check_no_uvars = (uu___112_1275.check_no_uvars);
            unmeta = (uu___112_1275.unmeta);
            unascribe = (uu___112_1275.unascribe)
          }
      | EraseUniverses  ->
          let uu___113_1276 = fs  in
          {
            beta = (uu___113_1276.beta);
            iota = (uu___113_1276.iota);
            zeta = (uu___113_1276.zeta);
            weak = (uu___113_1276.weak);
            hnf = (uu___113_1276.hnf);
            primops = (uu___113_1276.primops);
            no_delta_steps = (uu___113_1276.no_delta_steps);
            unfold_until = (uu___113_1276.unfold_until);
            unfold_only = (uu___113_1276.unfold_only);
            unfold_fully = (uu___113_1276.unfold_fully);
            unfold_attr = (uu___113_1276.unfold_attr);
            unfold_tac = (uu___113_1276.unfold_tac);
            pure_subterms_within_computations =
              (uu___113_1276.pure_subterms_within_computations);
            simplify = (uu___113_1276.simplify);
            erase_universes = true;
            allow_unbound_universes = (uu___113_1276.allow_unbound_universes);
            reify_ = (uu___113_1276.reify_);
            compress_uvars = (uu___113_1276.compress_uvars);
            no_full_norm = (uu___113_1276.no_full_norm);
            check_no_uvars = (uu___113_1276.check_no_uvars);
            unmeta = (uu___113_1276.unmeta);
            unascribe = (uu___113_1276.unascribe)
          }
      | AllowUnboundUniverses  ->
          let uu___114_1277 = fs  in
          {
            beta = (uu___114_1277.beta);
            iota = (uu___114_1277.iota);
            zeta = (uu___114_1277.zeta);
            weak = (uu___114_1277.weak);
            hnf = (uu___114_1277.hnf);
            primops = (uu___114_1277.primops);
            no_delta_steps = (uu___114_1277.no_delta_steps);
            unfold_until = (uu___114_1277.unfold_until);
            unfold_only = (uu___114_1277.unfold_only);
            unfold_fully = (uu___114_1277.unfold_fully);
            unfold_attr = (uu___114_1277.unfold_attr);
            unfold_tac = (uu___114_1277.unfold_tac);
            pure_subterms_within_computations =
              (uu___114_1277.pure_subterms_within_computations);
            simplify = (uu___114_1277.simplify);
            erase_universes = (uu___114_1277.erase_universes);
            allow_unbound_universes = true;
            reify_ = (uu___114_1277.reify_);
            compress_uvars = (uu___114_1277.compress_uvars);
            no_full_norm = (uu___114_1277.no_full_norm);
            check_no_uvars = (uu___114_1277.check_no_uvars);
            unmeta = (uu___114_1277.unmeta);
            unascribe = (uu___114_1277.unascribe)
          }
      | Reify  ->
          let uu___115_1278 = fs  in
          {
            beta = (uu___115_1278.beta);
            iota = (uu___115_1278.iota);
            zeta = (uu___115_1278.zeta);
            weak = (uu___115_1278.weak);
            hnf = (uu___115_1278.hnf);
            primops = (uu___115_1278.primops);
            no_delta_steps = (uu___115_1278.no_delta_steps);
            unfold_until = (uu___115_1278.unfold_until);
            unfold_only = (uu___115_1278.unfold_only);
            unfold_fully = (uu___115_1278.unfold_fully);
            unfold_attr = (uu___115_1278.unfold_attr);
            unfold_tac = (uu___115_1278.unfold_tac);
            pure_subterms_within_computations =
              (uu___115_1278.pure_subterms_within_computations);
            simplify = (uu___115_1278.simplify);
            erase_universes = (uu___115_1278.erase_universes);
            allow_unbound_universes = (uu___115_1278.allow_unbound_universes);
            reify_ = true;
            compress_uvars = (uu___115_1278.compress_uvars);
            no_full_norm = (uu___115_1278.no_full_norm);
            check_no_uvars = (uu___115_1278.check_no_uvars);
            unmeta = (uu___115_1278.unmeta);
            unascribe = (uu___115_1278.unascribe)
          }
      | CompressUvars  ->
          let uu___116_1279 = fs  in
          {
            beta = (uu___116_1279.beta);
            iota = (uu___116_1279.iota);
            zeta = (uu___116_1279.zeta);
            weak = (uu___116_1279.weak);
            hnf = (uu___116_1279.hnf);
            primops = (uu___116_1279.primops);
            no_delta_steps = (uu___116_1279.no_delta_steps);
            unfold_until = (uu___116_1279.unfold_until);
            unfold_only = (uu___116_1279.unfold_only);
            unfold_fully = (uu___116_1279.unfold_fully);
            unfold_attr = (uu___116_1279.unfold_attr);
            unfold_tac = (uu___116_1279.unfold_tac);
            pure_subterms_within_computations =
              (uu___116_1279.pure_subterms_within_computations);
            simplify = (uu___116_1279.simplify);
            erase_universes = (uu___116_1279.erase_universes);
            allow_unbound_universes = (uu___116_1279.allow_unbound_universes);
            reify_ = (uu___116_1279.reify_);
            compress_uvars = true;
            no_full_norm = (uu___116_1279.no_full_norm);
            check_no_uvars = (uu___116_1279.check_no_uvars);
            unmeta = (uu___116_1279.unmeta);
            unascribe = (uu___116_1279.unascribe)
          }
      | NoFullNorm  ->
          let uu___117_1280 = fs  in
          {
            beta = (uu___117_1280.beta);
            iota = (uu___117_1280.iota);
            zeta = (uu___117_1280.zeta);
            weak = (uu___117_1280.weak);
            hnf = (uu___117_1280.hnf);
            primops = (uu___117_1280.primops);
            no_delta_steps = (uu___117_1280.no_delta_steps);
            unfold_until = (uu___117_1280.unfold_until);
            unfold_only = (uu___117_1280.unfold_only);
            unfold_fully = (uu___117_1280.unfold_fully);
            unfold_attr = (uu___117_1280.unfold_attr);
            unfold_tac = (uu___117_1280.unfold_tac);
            pure_subterms_within_computations =
              (uu___117_1280.pure_subterms_within_computations);
            simplify = (uu___117_1280.simplify);
            erase_universes = (uu___117_1280.erase_universes);
            allow_unbound_universes = (uu___117_1280.allow_unbound_universes);
            reify_ = (uu___117_1280.reify_);
            compress_uvars = (uu___117_1280.compress_uvars);
            no_full_norm = true;
            check_no_uvars = (uu___117_1280.check_no_uvars);
            unmeta = (uu___117_1280.unmeta);
            unascribe = (uu___117_1280.unascribe)
          }
      | CheckNoUvars  ->
          let uu___118_1281 = fs  in
          {
            beta = (uu___118_1281.beta);
            iota = (uu___118_1281.iota);
            zeta = (uu___118_1281.zeta);
            weak = (uu___118_1281.weak);
            hnf = (uu___118_1281.hnf);
            primops = (uu___118_1281.primops);
            no_delta_steps = (uu___118_1281.no_delta_steps);
            unfold_until = (uu___118_1281.unfold_until);
            unfold_only = (uu___118_1281.unfold_only);
            unfold_fully = (uu___118_1281.unfold_fully);
            unfold_attr = (uu___118_1281.unfold_attr);
            unfold_tac = (uu___118_1281.unfold_tac);
            pure_subterms_within_computations =
              (uu___118_1281.pure_subterms_within_computations);
            simplify = (uu___118_1281.simplify);
            erase_universes = (uu___118_1281.erase_universes);
            allow_unbound_universes = (uu___118_1281.allow_unbound_universes);
            reify_ = (uu___118_1281.reify_);
            compress_uvars = (uu___118_1281.compress_uvars);
            no_full_norm = (uu___118_1281.no_full_norm);
            check_no_uvars = true;
            unmeta = (uu___118_1281.unmeta);
            unascribe = (uu___118_1281.unascribe)
          }
      | Unmeta  ->
          let uu___119_1282 = fs  in
          {
            beta = (uu___119_1282.beta);
            iota = (uu___119_1282.iota);
            zeta = (uu___119_1282.zeta);
            weak = (uu___119_1282.weak);
            hnf = (uu___119_1282.hnf);
            primops = (uu___119_1282.primops);
            no_delta_steps = (uu___119_1282.no_delta_steps);
            unfold_until = (uu___119_1282.unfold_until);
            unfold_only = (uu___119_1282.unfold_only);
            unfold_fully = (uu___119_1282.unfold_fully);
            unfold_attr = (uu___119_1282.unfold_attr);
            unfold_tac = (uu___119_1282.unfold_tac);
            pure_subterms_within_computations =
              (uu___119_1282.pure_subterms_within_computations);
            simplify = (uu___119_1282.simplify);
            erase_universes = (uu___119_1282.erase_universes);
            allow_unbound_universes = (uu___119_1282.allow_unbound_universes);
            reify_ = (uu___119_1282.reify_);
            compress_uvars = (uu___119_1282.compress_uvars);
            no_full_norm = (uu___119_1282.no_full_norm);
            check_no_uvars = (uu___119_1282.check_no_uvars);
            unmeta = true;
            unascribe = (uu___119_1282.unascribe)
          }
      | Unascribe  ->
          let uu___120_1283 = fs  in
          {
            beta = (uu___120_1283.beta);
            iota = (uu___120_1283.iota);
            zeta = (uu___120_1283.zeta);
            weak = (uu___120_1283.weak);
            hnf = (uu___120_1283.hnf);
            primops = (uu___120_1283.primops);
            no_delta_steps = (uu___120_1283.no_delta_steps);
            unfold_until = (uu___120_1283.unfold_until);
            unfold_only = (uu___120_1283.unfold_only);
            unfold_fully = (uu___120_1283.unfold_fully);
            unfold_attr = (uu___120_1283.unfold_attr);
            unfold_tac = (uu___120_1283.unfold_tac);
            pure_subterms_within_computations =
              (uu___120_1283.pure_subterms_within_computations);
            simplify = (uu___120_1283.simplify);
            erase_universes = (uu___120_1283.erase_universes);
            allow_unbound_universes = (uu___120_1283.allow_unbound_universes);
            reify_ = (uu___120_1283.reify_);
            compress_uvars = (uu___120_1283.compress_uvars);
            no_full_norm = (uu___120_1283.no_full_norm);
            check_no_uvars = (uu___120_1283.check_no_uvars);
            unmeta = (uu___120_1283.unmeta);
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
  { psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1322  -> []) } 
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
    match projectee with | Clos _0 -> true | uu____1565 -> false
  
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
    match projectee with | Univ _0 -> true | uu____1667 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____1678 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
let (closure_to_string : closure -> Prims.string) =
  fun uu___79_1697  ->
    match uu___79_1697 with
    | Clos (uu____1698,t,uu____1700,uu____1701) ->
        FStar_Syntax_Print.term_to_string t
    | Univ uu____1746 -> "Univ"
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
             let uu____1998 = FStar_Ident.text_of_lid p.name  in
             FStar_Util.psmap_add m1 uu____1998 p) l m
  
let (prim_from_list :
  primitive_step Prims.list -> primitive_step FStar_Util.psmap) =
  fun l  ->
    let uu____2010 = FStar_Util.psmap_empty ()  in add_steps uu____2010 l
  
let (find_prim_step :
  cfg ->
    FStar_Syntax_Syntax.fv -> primitive_step FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun fv  ->
      let uu____2021 =
        FStar_Ident.text_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      FStar_Util.psmap_try_find cfg.primitive_steps uu____2021
  
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
    match projectee with | Arg _0 -> true | uu____2163 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____2199 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____2235 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____2304 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_Range.range) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____2346 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____2402 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____2442 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____2474 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____2510 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____2526 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list[@@deriving show]
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____2551 = FStar_Syntax_Util.head_and_args' t  in
    match uu____2551 with | (hd1,uu____2565) -> hd1
  
let mk :
  'Auu____2585 .
    'Auu____2585 ->
      FStar_Range.range -> 'Auu____2585 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo : 'a . cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> Prims.unit =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.memoize_lazy
        then
          let uu____2639 = FStar_ST.op_Bang r  in
          match uu____2639 with
          | FStar_Pervasives_Native.Some uu____2687 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (env_to_string : closure Prims.list -> Prims.string) =
  fun env  ->
    let uu____2741 = FStar_List.map closure_to_string env  in
    FStar_All.pipe_right uu____2741 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___80_2748  ->
    match uu___80_2748 with
    | Arg (c,uu____2750,uu____2751) ->
        let uu____2752 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____2752
    | MemoLazy uu____2753 -> "MemoLazy"
    | Abs (uu____2760,bs,uu____2762,uu____2763,uu____2764) ->
        let uu____2769 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____2769
    | UnivArgs uu____2774 -> "UnivArgs"
    | Match uu____2781 -> "Match"
    | App (uu____2788,t,uu____2790,uu____2791) ->
        let uu____2792 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2792
    | Meta (m,uu____2794) -> "Meta"
    | Let uu____2795 -> "Let"
    | Cfg uu____2804 -> "Cfg"
    | Debug (t,uu____2806) ->
        let uu____2807 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2807
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2815 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2815 (FStar_String.concat "; ")
  
let (log : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).gen then f () else () 
let (log_primops : cfg -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun cfg  -> fun f  -> if (cfg.debug).primop then f () else () 
let is_empty : 'Auu____2846 . 'Auu____2846 Prims.list -> Prims.bool =
  fun uu___81_2852  ->
    match uu___81_2852 with | [] -> true | uu____2855 -> false
  
let lookup_bvar :
  'Auu____2862 'Auu____2863 .
    ('Auu____2862,'Auu____2863) FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.bv -> 'Auu____2863
  =
  fun env  ->
    fun x  ->
      try
        let uu____2887 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____2887
      with
      | uu____2900 ->
          let uu____2901 =
            let uu____2902 = FStar_Syntax_Print.db_to_string x  in
            FStar_Util.format1 "Failed to find %s\n" uu____2902  in
          failwith uu____2901
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____2908 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____2908
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____2912 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____2912
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____2916 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____2916
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
          let uu____2942 =
            FStar_List.fold_left
              (fun uu____2968  ->
                 fun u1  ->
                   match uu____2968 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2993 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2993 with
                        | (k_u,n1) ->
                            let uu____3008 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____3008
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2942 with
          | (uu____3026,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____3051 =
                   let uu____3052 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____3052  in
                 match uu____3051 with
                 | Univ u3 -> aux u3
                 | Dummy  -> [u2]
                 | uu____3070 ->
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____3078 ->
                   if (cfg.steps).allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____3084 when
              (cfg.steps).check_no_uvars -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____3093 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____3102 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____3109 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____3109 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____3126 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____3126 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____3134 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____3142 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____3142 with
                                  | (uu____3147,m) -> n1 <= m))
                           in
                        if uu____3134 then rest1 else us1
                    | uu____3152 -> us1)
               | uu____3157 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____3161 = aux u3  in
              FStar_List.map (fun _0_40  -> FStar_Syntax_Syntax.U_succ _0_40)
                uu____3161
           in
        if (cfg.steps).erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____3165 = aux u  in
           match uu____3165 with
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
          (fun uu____3269  ->
             let uu____3270 = FStar_Syntax_Print.tag_of_term t  in
             let uu____3271 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 ">>> %s Closure_as_term %s\n" uu____3270
               uu____3271);
        (match env with
         | [] when
             FStar_All.pipe_left Prims.op_Negation (cfg.steps).compress_uvars
             -> t
         | uu____3278 ->
             let t1 = FStar_Syntax_Subst.compress t  in
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_delayed uu____3280 ->
                  failwith "Impossible"
              | FStar_Syntax_Syntax.Tm_unknown  -> t1
              | FStar_Syntax_Syntax.Tm_constant uu____3305 -> t1
              | FStar_Syntax_Syntax.Tm_name uu____3306 -> t1
              | FStar_Syntax_Syntax.Tm_lazy uu____3307 -> t1
              | FStar_Syntax_Syntax.Tm_fvar uu____3308 -> t1
              | FStar_Syntax_Syntax.Tm_uvar uu____3309 ->
                  if (cfg.steps).check_no_uvars
                  then
                    let uu____3326 =
                      let uu____3327 =
                        FStar_Range.string_of_range
                          t1.FStar_Syntax_Syntax.pos
                         in
                      let uu____3328 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.format2
                        "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                        uu____3327 uu____3328
                       in
                    failwith uu____3326
                  else t1
              | FStar_Syntax_Syntax.Tm_type u ->
                  let uu____3331 =
                    let uu____3332 = norm_universe cfg env u  in
                    FStar_Syntax_Syntax.Tm_type uu____3332  in
                  mk uu____3331 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  let uu____3339 = FStar_List.map (norm_universe cfg env) us
                     in
                  FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3339
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____3341 = lookup_bvar env x  in
                  (match uu____3341 with
                   | Univ uu____3344 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> t1
                   | Clos (env1,t0,uu____3347,uu____3348) ->
                       closure_as_term cfg env1 t0)
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let head2 = closure_as_term_delayed cfg env head1  in
                  let args1 = closures_as_args_delayed cfg env args  in
                  mk (FStar_Syntax_Syntax.Tm_app (head2, args1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  let uu____3460 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3460 with
                   | (bs1,env1) ->
                       let body1 = closure_as_term_delayed cfg env1 body  in
                       let uu____3488 =
                         let uu____3489 =
                           let uu____3506 = close_lcomp_opt cfg env1 lopt  in
                           (bs1, body1, uu____3506)  in
                         FStar_Syntax_Syntax.Tm_abs uu____3489  in
                       mk uu____3488 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  let uu____3537 = closures_as_binders_delayed cfg env bs  in
                  (match uu____3537 with
                   | (bs1,env1) ->
                       let c1 = close_comp cfg env1 c  in
                       mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                  let uu____3579 =
                    let uu____3590 =
                      let uu____3597 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3597]  in
                    closures_as_binders_delayed cfg env uu____3590  in
                  (match uu____3579 with
                   | (x1,env1) ->
                       let phi1 = closure_as_term_delayed cfg env1 phi  in
                       let uu____3615 =
                         let uu____3616 =
                           let uu____3623 =
                             let uu____3624 = FStar_List.hd x1  in
                             FStar_All.pipe_right uu____3624
                               FStar_Pervasives_Native.fst
                              in
                           (uu____3623, phi1)  in
                         FStar_Syntax_Syntax.Tm_refine uu____3616  in
                       mk uu____3615 t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(annot,tacopt),lopt) ->
                  let annot1 =
                    match annot with
                    | FStar_Util.Inl t2 ->
                        let uu____3715 = closure_as_term_delayed cfg env t2
                           in
                        FStar_Util.Inl uu____3715
                    | FStar_Util.Inr c ->
                        let uu____3729 = close_comp cfg env c  in
                        FStar_Util.Inr uu____3729
                     in
                  let tacopt1 =
                    FStar_Util.map_opt tacopt
                      (closure_as_term_delayed cfg env)
                     in
                  let uu____3745 =
                    let uu____3746 =
                      let uu____3773 = closure_as_term_delayed cfg env t11
                         in
                      (uu____3773, (annot1, tacopt1), lopt)  in
                    FStar_Syntax_Syntax.Tm_ascribed uu____3746  in
                  mk uu____3745 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                  (match qi.FStar_Syntax_Syntax.qkind with
                   | FStar_Syntax_Syntax.Quote_dynamic  ->
                       let uu____3814 =
                         let uu____3815 =
                           let uu____3822 =
                             closure_as_term_delayed cfg env t'  in
                           (uu____3822, qi)  in
                         FStar_Syntax_Syntax.Tm_quoted uu____3815  in
                       mk uu____3814 t1.FStar_Syntax_Syntax.pos
                   | FStar_Syntax_Syntax.Quote_static  ->
                       let qi1 =
                         FStar_Syntax_Syntax.on_antiquoted
                           (closure_as_term_delayed cfg env) qi
                          in
                       mk (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_pattern args) ->
                  let uu____3846 =
                    let uu____3847 =
                      let uu____3854 = closure_as_term_delayed cfg env t'  in
                      let uu____3857 =
                        let uu____3858 =
                          FStar_All.pipe_right args
                            (FStar_List.map
                               (closures_as_args_delayed cfg env))
                           in
                        FStar_Syntax_Syntax.Meta_pattern uu____3858  in
                      (uu____3854, uu____3857)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3847  in
                  mk uu____3846 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic (m,tbody)) ->
                  let uu____3918 =
                    let uu____3919 =
                      let uu____3926 = closure_as_term_delayed cfg env t'  in
                      let uu____3929 =
                        let uu____3930 =
                          let uu____3937 =
                            closure_as_term_delayed cfg env tbody  in
                          (m, uu____3937)  in
                        FStar_Syntax_Syntax.Meta_monadic uu____3930  in
                      (uu____3926, uu____3929)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3919  in
                  mk uu____3918 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta
                  (t',FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody)) ->
                  let uu____3956 =
                    let uu____3957 =
                      let uu____3964 = closure_as_term_delayed cfg env t'  in
                      let uu____3967 =
                        let uu____3968 =
                          let uu____3977 =
                            closure_as_term_delayed cfg env tbody  in
                          (m1, m2, uu____3977)  in
                        FStar_Syntax_Syntax.Meta_monadic_lift uu____3968  in
                      (uu____3964, uu____3967)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3957  in
                  mk uu____3956 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                  let uu____3990 =
                    let uu____3991 =
                      let uu____3998 = closure_as_term_delayed cfg env t'  in
                      (uu____3998, m)  in
                    FStar_Syntax_Syntax.Tm_meta uu____3991  in
                  mk uu____3990 t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let env0 = env  in
                  let env1 =
                    FStar_List.fold_left
                      (fun env1  -> fun uu____4038  -> dummy :: env1) env
                      lb.FStar_Syntax_Syntax.lbunivs
                     in
                  let typ =
                    closure_as_term_delayed cfg env1
                      lb.FStar_Syntax_Syntax.lbtyp
                     in
                  let def =
                    closure_as_term cfg env1 lb.FStar_Syntax_Syntax.lbdef  in
                  let uu____4057 =
                    let uu____4068 = FStar_Syntax_Syntax.is_top_level [lb]
                       in
                    if uu____4068
                    then ((lb.FStar_Syntax_Syntax.lbname), body)
                    else
                      (let x = FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                          in
                       let uu____4087 =
                         closure_as_term cfg (dummy :: env0) body  in
                       ((FStar_Util.Inl
                           (let uu___125_4099 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___125_4099.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___125_4099.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = typ
                            })), uu____4087))
                     in
                  (match uu____4057 with
                   | (nm,body1) ->
                       let lb1 =
                         let uu___126_4115 = lb  in
                         {
                           FStar_Syntax_Syntax.lbname = nm;
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___126_4115.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = typ;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___126_4115.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = def;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___126_4115.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___126_4115.FStar_Syntax_Syntax.lbpos)
                         }  in
                       mk
                         (FStar_Syntax_Syntax.Tm_let ((false, [lb1]), body1))
                         t1.FStar_Syntax_Syntax.pos)
              | FStar_Syntax_Syntax.Tm_let ((uu____4126,lbs),body) ->
                  let norm_one_lb env1 lb =
                    let env_univs =
                      FStar_List.fold_right
                        (fun uu____4185  -> fun env2  -> dummy :: env2)
                        lb.FStar_Syntax_Syntax.lbunivs env1
                       in
                    let env2 =
                      let uu____4210 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4210
                      then env_univs
                      else
                        FStar_List.fold_right
                          (fun uu____4230  -> fun env2  -> dummy :: env2) lbs
                          env_univs
                       in
                    let ty =
                      closure_as_term cfg env_univs
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let nm =
                      let uu____4252 = FStar_Syntax_Syntax.is_top_level lbs
                         in
                      if uu____4252
                      then lb.FStar_Syntax_Syntax.lbname
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         FStar_All.pipe_right
                           (let uu___127_4264 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___127_4264.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___127_4264.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = ty
                            }) (fun _0_41  -> FStar_Util.Inl _0_41))
                       in
                    let uu___128_4265 = lb  in
                    let uu____4266 =
                      closure_as_term cfg env2 lb.FStar_Syntax_Syntax.lbdef
                       in
                    {
                      FStar_Syntax_Syntax.lbname = nm;
                      FStar_Syntax_Syntax.lbunivs =
                        (uu___128_4265.FStar_Syntax_Syntax.lbunivs);
                      FStar_Syntax_Syntax.lbtyp = ty;
                      FStar_Syntax_Syntax.lbeff =
                        (uu___128_4265.FStar_Syntax_Syntax.lbeff);
                      FStar_Syntax_Syntax.lbdef = uu____4266;
                      FStar_Syntax_Syntax.lbattrs =
                        (uu___128_4265.FStar_Syntax_Syntax.lbattrs);
                      FStar_Syntax_Syntax.lbpos =
                        (uu___128_4265.FStar_Syntax_Syntax.lbpos)
                    }  in
                  let lbs1 =
                    FStar_All.pipe_right lbs
                      (FStar_List.map (norm_one_lb env))
                     in
                  let body1 =
                    let body_env =
                      FStar_List.fold_right
                        (fun uu____4296  -> fun env1  -> dummy :: env1) lbs1
                        env
                       in
                    closure_as_term cfg body_env body  in
                  mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                    t1.FStar_Syntax_Syntax.pos
              | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                  let head2 = closure_as_term cfg env head1  in
                  let norm_one_branch env1 uu____4385 =
                    match uu____4385 with
                    | (pat,w_opt,tm) ->
                        let rec norm_pat env2 p =
                          match p.FStar_Syntax_Syntax.v with
                          | FStar_Syntax_Syntax.Pat_constant uu____4440 ->
                              (p, env2)
                          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                              let uu____4461 =
                                FStar_All.pipe_right pats
                                  (FStar_List.fold_left
                                     (fun uu____4521  ->
                                        fun uu____4522  ->
                                          match (uu____4521, uu____4522) with
                                          | ((pats1,env3),(p1,b)) ->
                                              let uu____4613 =
                                                norm_pat env3 p1  in
                                              (match uu____4613 with
                                               | (p2,env4) ->
                                                   (((p2, b) :: pats1), env4)))
                                     ([], env2))
                                 in
                              (match uu____4461 with
                               | (pats1,env3) ->
                                   ((let uu___129_4695 = p  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv, (FStar_List.rev pats1)));
                                       FStar_Syntax_Syntax.p =
                                         (uu___129_4695.FStar_Syntax_Syntax.p)
                                     }), env3))
                          | FStar_Syntax_Syntax.Pat_var x ->
                              let x1 =
                                let uu___130_4714 = x  in
                                let uu____4715 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___130_4714.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___130_4714.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4715
                                }  in
                              ((let uu___131_4729 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_var x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___131_4729.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_wild x ->
                              let x1 =
                                let uu___132_4740 = x  in
                                let uu____4741 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___132_4740.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___132_4740.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4741
                                }  in
                              ((let uu___133_4755 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_wild x1);
                                  FStar_Syntax_Syntax.p =
                                    (uu___133_4755.FStar_Syntax_Syntax.p)
                                }), (dummy :: env2))
                          | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                              let x1 =
                                let uu___134_4771 = x  in
                                let uu____4772 =
                                  closure_as_term cfg env2
                                    x.FStar_Syntax_Syntax.sort
                                   in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___134_4771.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___134_4771.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = uu____4772
                                }  in
                              let t3 = closure_as_term cfg env2 t2  in
                              ((let uu___135_4779 = p  in
                                {
                                  FStar_Syntax_Syntax.v =
                                    (FStar_Syntax_Syntax.Pat_dot_term
                                       (x1, t3));
                                  FStar_Syntax_Syntax.p =
                                    (uu___135_4779.FStar_Syntax_Syntax.p)
                                }), env2)
                           in
                        let uu____4782 = norm_pat env1 pat  in
                        (match uu____4782 with
                         | (pat1,env2) ->
                             let w_opt1 =
                               match w_opt with
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Pervasives_Native.None
                               | FStar_Pervasives_Native.Some w ->
                                   let uu____4811 =
                                     closure_as_term cfg env2 w  in
                                   FStar_Pervasives_Native.Some uu____4811
                                in
                             let tm1 = closure_as_term cfg env2 tm  in
                             (pat1, w_opt1, tm1))
                     in
                  let uu____4817 =
                    let uu____4818 =
                      let uu____4841 =
                        FStar_All.pipe_right branches
                          (FStar_List.map (norm_one_branch env))
                         in
                      (head2, uu____4841)  in
                    FStar_Syntax_Syntax.Tm_match uu____4818  in
                  mk uu____4817 t1.FStar_Syntax_Syntax.pos))

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
        | uu____4927 -> closure_as_term cfg env t

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
        | uu____4953 ->
            FStar_List.map
              (fun uu____4970  ->
                 match uu____4970 with
                 | (x,imp) ->
                     let uu____4989 = closure_as_term_delayed cfg env x  in
                     (uu____4989, imp)) args

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
        let uu____5003 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____5052  ->
                  fun uu____5053  ->
                    match (uu____5052, uu____5053) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___136_5123 = b  in
                          let uu____5124 =
                            closure_as_term_delayed cfg env1
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___136_5123.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___136_5123.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____5124
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____5003 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____5217 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5230 = closure_as_term_delayed cfg env t  in
                 let uu____5231 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5230 uu____5231
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5244 = closure_as_term_delayed cfg env t  in
                 let uu____5245 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5244 uu____5245
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
                        (fun uu___82_5271  ->
                           match uu___82_5271 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5275 =
                                 closure_as_term_delayed cfg env t  in
                               FStar_Syntax_Syntax.DECREASES uu____5275
                           | f -> f))
                    in
                 let uu____5279 =
                   let uu___137_5280 = c1  in
                   let uu____5281 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5281;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___137_5280.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5279)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___83_5291  ->
            match uu___83_5291 with
            | FStar_Syntax_Syntax.DECREASES uu____5292 -> false
            | uu____5295 -> true))

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
                   (fun uu___84_5313  ->
                      match uu___84_5313 with
                      | FStar_Syntax_Syntax.DECREASES uu____5314 -> false
                      | uu____5317 -> true))
               in
            let rc1 =
              let uu___138_5319 = rc  in
              let uu____5320 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (closure_as_term cfg env)
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___138_5319.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5320;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5327 -> lopt

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
    let uu____5409 =
      let uu____5416 = FStar_Syntax_Embeddings.e_list e  in
      FStar_Syntax_Embeddings.try_unembed uu____5416  in
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5409  in
  let arg_as_bounded_int uu____5440 =
    match uu____5440 with
    | (a,uu____5452) ->
        let uu____5459 =
          let uu____5460 = FStar_Syntax_Subst.compress a  in
          uu____5460.FStar_Syntax_Syntax.n  in
        (match uu____5459 with
         | FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv1;
                FStar_Syntax_Syntax.pos = uu____5470;
                FStar_Syntax_Syntax.vars = uu____5471;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_constant
                                                              (FStar_Const.Const_int
                                                              (i,FStar_Pervasives_Native.None
                                                               ));
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____5473;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____5474;_},uu____5475)::[])
             when
             let uu____5514 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____5514 "int_to_t" ->
             let uu____5515 =
               let uu____5520 = FStar_BigInt.big_int_of_string i  in
               (fv1, uu____5520)  in
             FStar_Pervasives_Native.Some uu____5515
         | uu____5525 -> FStar_Pervasives_Native.None)
     in
  let lift_unary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a)::[] ->
        let uu____5565 = f a  in FStar_Pervasives_Native.Some uu____5565
    | uu____5566 -> FStar_Pervasives_Native.None  in
  let lift_binary a b f aopts =
    match aopts with
    | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
        a1)::[] ->
        let uu____5614 = f a0 a1  in FStar_Pervasives_Native.Some uu____5614
    | uu____5615 -> FStar_Pervasives_Native.None  in
  let unary_op a394 a395 a396 a397 a398 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5657 = FStar_List.map as_a args  in
                  lift_unary () ()
                    (fun a393  -> (Obj.magic (f res.psc_range)) a393)
                    uu____5657)) a394 a395 a396 a397 a398
     in
  let binary_op a401 a402 a403 a404 a405 =
    (Obj.magic
       (fun a  ->
          fun as_a  ->
            fun f  ->
              fun res  ->
                fun args  ->
                  let uu____5706 = FStar_List.map as_a args  in
                  lift_binary () ()
                    (fun a399  ->
                       fun a400  -> (Obj.magic (f res.psc_range)) a399 a400)
                    uu____5706)) a401 a402 a403 a404 a405
     in
  let as_primitive_step is_strong uu____5733 =
    match uu____5733 with
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
                   let uu____5781 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_int r uu____5781)) a407 a408)
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
                       let uu____5809 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_int r uu____5809)) a410
               a411 a412)
     in
  let unary_bool_op f =
    unary_op () (fun a413  -> (Obj.magic arg_as_bool) a413)
      (fun a414  ->
         fun a415  ->
           (Obj.magic
              (fun r  ->
                 fun x  ->
                   let uu____5830 = f x  in
                   FStar_Syntax_Embeddings.embed
                     FStar_Syntax_Embeddings.e_bool r uu____5830)) a414 a415)
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
                       let uu____5858 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_bool r uu____5858)) a417
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
                       let uu____5886 = f x y  in
                       FStar_Syntax_Embeddings.embed
                         FStar_Syntax_Embeddings.e_string r uu____5886)) a421
               a422 a423)
     in
  let mixed_binary_op a b c as_a as_b embed_c f res args =
    match args with
    | a::b::[] ->
        let uu____5994 =
          let uu____6003 = as_a a  in
          let uu____6006 = as_b b  in (uu____6003, uu____6006)  in
        (match uu____5994 with
         | (FStar_Pervasives_Native.Some a1,FStar_Pervasives_Native.Some b1)
             ->
             let uu____6021 =
               let uu____6022 = f res.psc_range a1 b1  in
               embed_c res.psc_range uu____6022  in
             FStar_Pervasives_Native.Some uu____6021
         | uu____6023 -> FStar_Pervasives_Native.None)
    | uu____6032 -> FStar_Pervasives_Native.None  in
  let list_of_string' rng s =
    let name l =
      let uu____6046 =
        let uu____6047 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
            FStar_Pervasives_Native.None
           in
        FStar_Syntax_Syntax.Tm_fvar uu____6047  in
      mk uu____6046 rng  in
    let char_t = name FStar_Parser_Const.char_lid  in
    let charterm c =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng  in
    let uu____6057 =
      let uu____6060 = FStar_String.list_of_string s  in
      FStar_List.map charterm uu____6060  in
    FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____6057  in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l  in FStar_Syntax_Util.exp_string s
     in
  let string_compare' rng s1 s2 =
    let r = FStar_String.compare s1 s2  in
    let uu____6092 =
      let uu____6093 = FStar_Util.string_of_int r  in
      FStar_BigInt.big_int_of_string uu____6093  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng
      uu____6092
     in
  let string_concat' psc args =
    match args with
    | a1::a2::[] ->
        let uu____6111 = arg_as_string a1  in
        (match uu____6111 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6117 =
               Obj.magic
                 (arg_as_list () (Obj.magic FStar_Syntax_Embeddings.e_string)
                    a2)
                in
             (match uu____6117 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____6130 =
                    FStar_Syntax_Embeddings.embed
                      FStar_Syntax_Embeddings.e_string psc.psc_range r
                     in
                  FStar_Pervasives_Native.Some uu____6130
              | uu____6131 -> FStar_Pervasives_Native.None)
         | uu____6136 -> FStar_Pervasives_Native.None)
    | uu____6139 -> FStar_Pervasives_Native.None  in
  let string_of_int1 rng i =
    let uu____6149 = FStar_BigInt.string_of_big_int i  in
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      uu____6149
     in
  let string_of_bool1 rng b =
    FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false")
     in
  let mk_range1 psc args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6178 =
          let uu____6199 = arg_as_string fn  in
          let uu____6202 = arg_as_int from_line  in
          let uu____6205 = arg_as_int from_col  in
          let uu____6208 = arg_as_int to_line  in
          let uu____6211 = arg_as_int to_col  in
          (uu____6199, uu____6202, uu____6205, uu____6208, uu____6211)  in
        (match uu____6178 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6242 =
                 let uu____6243 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6244 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6243 uu____6244  in
               let uu____6245 =
                 let uu____6246 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6247 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6246 uu____6247  in
               FStar_Range.mk_range fn1 uu____6242 uu____6245  in
             let uu____6248 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6248
         | uu____6249 -> FStar_Pervasives_Native.None)
    | uu____6270 -> FStar_Pervasives_Native.None  in
  let decidable_eq neg psc args =
    let r = psc.psc_range  in
    let tru =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r
       in
    let fal =
      mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r
       in
    match args with
    | (_typ,uu____6297)::(a1,uu____6299)::(a2,uu____6301)::[] ->
        let uu____6338 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____6338 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu____6351 -> FStar_Pervasives_Native.None)
    | uu____6352 -> failwith "Unexpected number of arguments"  in
  let prims_to_fstar_range_step psc args =
    match args with
    | (a1,uu____6379)::[] ->
        let uu____6388 =
          FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range
            a1
           in
        (match uu____6388 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6394 =
               FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range
                 psc.psc_range r
                in
             FStar_Pervasives_Native.Some uu____6394
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6395 -> failwith "Unexpected number of arguments"  in
  let basic_ops =
    let uu____6419 =
      let uu____6434 =
        let uu____6449 =
          let uu____6464 =
            let uu____6479 =
              let uu____6494 =
                let uu____6509 =
                  let uu____6524 =
                    let uu____6539 =
                      let uu____6554 =
                        let uu____6569 =
                          let uu____6584 =
                            let uu____6599 =
                              let uu____6614 =
                                let uu____6629 =
                                  let uu____6644 =
                                    let uu____6659 =
                                      let uu____6674 =
                                        let uu____6689 =
                                          let uu____6704 =
                                            let uu____6719 =
                                              let uu____6734 =
                                                let uu____6747 =
                                                  FStar_Parser_Const.p2l
                                                    ["FStar";
                                                    "String";
                                                    "list_of_string"]
                                                   in
                                                (uu____6747,
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
                                              let uu____6754 =
                                                let uu____6769 =
                                                  let uu____6782 =
                                                    FStar_Parser_Const.p2l
                                                      ["FStar";
                                                      "String";
                                                      "string_of_list"]
                                                     in
                                                  (uu____6782,
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
                                                let uu____6789 =
                                                  let uu____6804 =
                                                    let uu____6819 =
                                                      FStar_Parser_Const.p2l
                                                        ["FStar";
                                                        "String";
                                                        "concat"]
                                                       in
                                                    (uu____6819,
                                                      (Prims.parse_int "2"),
                                                      string_concat')
                                                     in
                                                  let uu____6828 =
                                                    let uu____6845 =
                                                      let uu____6860 =
                                                        FStar_Parser_Const.p2l
                                                          ["Prims";
                                                          "mk_range"]
                                                         in
                                                      (uu____6860,
                                                        (Prims.parse_int "5"),
                                                        mk_range1)
                                                       in
                                                    [uu____6845]  in
                                                  uu____6804 :: uu____6828
                                                   in
                                                uu____6769 :: uu____6789  in
                                              uu____6734 :: uu____6754  in
                                            (FStar_Parser_Const.op_notEq,
                                              (Prims.parse_int "3"),
                                              (decidable_eq true)) ::
                                              uu____6719
                                             in
                                          (FStar_Parser_Const.op_Eq,
                                            (Prims.parse_int "3"),
                                            (decidable_eq false)) ::
                                            uu____6704
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
                                          :: uu____6689
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
                                        :: uu____6674
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
                                      :: uu____6659
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
                                                        let uu____7051 =
                                                          FStar_BigInt.to_int_fs
                                                            x
                                                           in
                                                        FStar_String.make
                                                          uu____7051 y)) a444
                                                a445 a446)))
                                    :: uu____6644
                                   in
                                (FStar_Parser_Const.strcat_lid',
                                  (Prims.parse_int "2"),
                                  (binary_string_op
                                     (fun x  -> fun y  -> Prims.strcat x y)))
                                  :: uu____6629
                                 in
                              (FStar_Parser_Const.strcat_lid,
                                (Prims.parse_int "2"),
                                (binary_string_op
                                   (fun x  -> fun y  -> Prims.strcat x y)))
                                :: uu____6614
                               in
                            (FStar_Parser_Const.op_Or, (Prims.parse_int "2"),
                              (binary_bool_op (fun x  -> fun y  -> x || y)))
                              :: uu____6599
                             in
                          (FStar_Parser_Const.op_And, (Prims.parse_int "2"),
                            (binary_bool_op (fun x  -> fun y  -> x && y))) ::
                            uu____6584
                           in
                        (FStar_Parser_Const.op_Negation,
                          (Prims.parse_int "1"),
                          (unary_bool_op (fun x  -> Prims.op_Negation x))) ::
                          uu____6569
                         in
                      (FStar_Parser_Const.op_Modulus, (Prims.parse_int "2"),
                        (binary_int_op
                           (fun x  -> fun y  -> FStar_BigInt.mod_big_int x y)))
                        :: uu____6554
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
                                          let uu____7218 =
                                            FStar_BigInt.ge_big_int x y  in
                                          FStar_Syntax_Embeddings.embed
                                            FStar_Syntax_Embeddings.e_bool r
                                            uu____7218)) a448 a449 a450)))
                      :: uu____6539
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
                                        let uu____7244 =
                                          FStar_BigInt.gt_big_int x y  in
                                        FStar_Syntax_Embeddings.embed
                                          FStar_Syntax_Embeddings.e_bool r
                                          uu____7244)) a452 a453 a454)))
                    :: uu____6524
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
                                      let uu____7270 =
                                        FStar_BigInt.le_big_int x y  in
                                      FStar_Syntax_Embeddings.embed
                                        FStar_Syntax_Embeddings.e_bool r
                                        uu____7270)) a456 a457 a458)))
                  :: uu____6509
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
                                    let uu____7296 =
                                      FStar_BigInt.lt_big_int x y  in
                                    FStar_Syntax_Embeddings.embed
                                      FStar_Syntax_Embeddings.e_bool r
                                      uu____7296)) a460 a461 a462)))
                :: uu____6494
               in
            (FStar_Parser_Const.op_Division, (Prims.parse_int "2"),
              (binary_int_op
                 (fun x  -> fun y  -> FStar_BigInt.div_big_int x y)))
              :: uu____6479
             in
          (FStar_Parser_Const.op_Multiply, (Prims.parse_int "2"),
            (binary_int_op
               (fun x  -> fun y  -> FStar_BigInt.mult_big_int x y)))
            :: uu____6464
           in
        (FStar_Parser_Const.op_Subtraction, (Prims.parse_int "2"),
          (binary_int_op (fun x  -> fun y  -> FStar_BigInt.sub_big_int x y)))
          :: uu____6449
         in
      (FStar_Parser_Const.op_Addition, (Prims.parse_int "2"),
        (binary_int_op (fun x  -> fun y  -> FStar_BigInt.add_big_int x y)))
        :: uu____6434
       in
    (FStar_Parser_Const.op_Minus, (Prims.parse_int "1"),
      (unary_int_op (fun x  -> FStar_BigInt.minus_big_int x))) :: uu____6419
     in
  let weak_ops =
    let uu____7435 =
      let uu____7454 =
        FStar_Parser_Const.p2l ["FStar"; "Range"; "prims_to_fstar_range"]  in
      (uu____7454, (Prims.parse_int "1"), prims_to_fstar_range_step)  in
    [uu____7435]  in
  let bounded_arith_ops =
    let bounded_signed_int_types = ["Int8"; "Int16"; "Int32"; "Int64"]  in
    let bounded_unsigned_int_types =
      ["UInt8"; "UInt16"; "UInt32"; "UInt64"; "UInt128"]  in
    let int_as_bounded r int_to_t1 n1 =
      let c =
        FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1  in
      let int_to_t2 = FStar_Syntax_Syntax.fv_to_tm int_to_t1  in
      let uu____7538 =
        let uu____7539 =
          let uu____7540 = FStar_Syntax_Syntax.as_arg c  in [uu____7540]  in
        FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____7539  in
      uu____7538 FStar_Pervasives_Native.None r  in
    let add_sub_mul_v =
      FStar_All.pipe_right
        (FStar_List.append bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_List.collect
           (fun m  ->
              let uu____7590 =
                let uu____7603 = FStar_Parser_Const.p2l ["FStar"; m; "add"]
                   in
                (uu____7603, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a463  -> (Obj.magic arg_as_bounded_int) a463)
                     (fun a464  ->
                        fun a465  ->
                          fun a466  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7619  ->
                                    fun uu____7620  ->
                                      match (uu____7619, uu____7620) with
                                      | ((int_to_t1,x),(uu____7639,y)) ->
                                          let uu____7649 =
                                            FStar_BigInt.add_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____7649)) a464 a465 a466)))
                 in
              let uu____7650 =
                let uu____7665 =
                  let uu____7678 = FStar_Parser_Const.p2l ["FStar"; m; "sub"]
                     in
                  (uu____7678, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a467  -> (Obj.magic arg_as_bounded_int) a467)
                       (fun a468  ->
                          fun a469  ->
                            fun a470  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____7694  ->
                                      fun uu____7695  ->
                                        match (uu____7694, uu____7695) with
                                        | ((int_to_t1,x),(uu____7714,y)) ->
                                            let uu____7724 =
                                              FStar_BigInt.sub_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____7724)) a468 a469 a470)))
                   in
                let uu____7725 =
                  let uu____7740 =
                    let uu____7753 =
                      FStar_Parser_Const.p2l ["FStar"; m; "mul"]  in
                    (uu____7753, (Prims.parse_int "2"),
                      (binary_op ()
                         (fun a471  -> (Obj.magic arg_as_bounded_int) a471)
                         (fun a472  ->
                            fun a473  ->
                              fun a474  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7769  ->
                                        fun uu____7770  ->
                                          match (uu____7769, uu____7770) with
                                          | ((int_to_t1,x),(uu____7789,y)) ->
                                              let uu____7799 =
                                                FStar_BigInt.mult_big_int x y
                                                 in
                                              int_as_bounded r int_to_t1
                                                uu____7799)) a472 a473 a474)))
                     in
                  let uu____7800 =
                    let uu____7815 =
                      let uu____7828 =
                        FStar_Parser_Const.p2l ["FStar"; m; "v"]  in
                      (uu____7828, (Prims.parse_int "1"),
                        (unary_op ()
                           (fun a475  -> (Obj.magic arg_as_bounded_int) a475)
                           (fun a476  ->
                              fun a477  ->
                                (Obj.magic
                                   (fun r  ->
                                      fun uu____7840  ->
                                        match uu____7840 with
                                        | (int_to_t1,x) ->
                                            FStar_Syntax_Embeddings.embed
                                              FStar_Syntax_Embeddings.e_int r
                                              x)) a476 a477)))
                       in
                    [uu____7815]  in
                  uu____7740 :: uu____7800  in
                uu____7665 :: uu____7725  in
              uu____7590 :: uu____7650))
       in
    let div_mod_unsigned =
      FStar_All.pipe_right bounded_unsigned_int_types
        (FStar_List.collect
           (fun m  ->
              let uu____7954 =
                let uu____7967 = FStar_Parser_Const.p2l ["FStar"; m; "div"]
                   in
                (uu____7967, (Prims.parse_int "2"),
                  (binary_op ()
                     (fun a478  -> (Obj.magic arg_as_bounded_int) a478)
                     (fun a479  ->
                        fun a480  ->
                          fun a481  ->
                            (Obj.magic
                               (fun r  ->
                                  fun uu____7983  ->
                                    fun uu____7984  ->
                                      match (uu____7983, uu____7984) with
                                      | ((int_to_t1,x),(uu____8003,y)) ->
                                          let uu____8013 =
                                            FStar_BigInt.div_big_int x y  in
                                          int_as_bounded r int_to_t1
                                            uu____8013)) a479 a480 a481)))
                 in
              let uu____8014 =
                let uu____8029 =
                  let uu____8042 = FStar_Parser_Const.p2l ["FStar"; m; "rem"]
                     in
                  (uu____8042, (Prims.parse_int "2"),
                    (binary_op ()
                       (fun a482  -> (Obj.magic arg_as_bounded_int) a482)
                       (fun a483  ->
                          fun a484  ->
                            fun a485  ->
                              (Obj.magic
                                 (fun r  ->
                                    fun uu____8058  ->
                                      fun uu____8059  ->
                                        match (uu____8058, uu____8059) with
                                        | ((int_to_t1,x),(uu____8078,y)) ->
                                            let uu____8088 =
                                              FStar_BigInt.mod_big_int x y
                                               in
                                            int_as_bounded r int_to_t1
                                              uu____8088)) a483 a484 a485)))
                   in
                [uu____8029]  in
              uu____7954 :: uu____8014))
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
    | (_typ,uu____8200)::(a1,uu____8202)::(a2,uu____8204)::[] ->
        let uu____8241 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8241 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___139_8247 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8247.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8247.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___140_8251 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___140_8251.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___140_8251.FStar_Syntax_Syntax.vars)
                })
         | uu____8252 -> FStar_Pervasives_Native.None)
    | (_typ,uu____8254)::uu____8255::(a1,uu____8257)::(a2,uu____8259)::[] ->
        let uu____8308 = FStar_Syntax_Util.eq_tm a1 a2  in
        (match uu____8308 with
         | FStar_Syntax_Util.Equal  ->
             FStar_Pervasives_Native.Some
               (let uu___139_8314 = FStar_Syntax_Util.t_true  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___139_8314.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___139_8314.FStar_Syntax_Syntax.vars)
                })
         | FStar_Syntax_Util.NotEqual  ->
             FStar_Pervasives_Native.Some
               (let uu___140_8318 = FStar_Syntax_Util.t_false  in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___140_8318.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = r;
                  FStar_Syntax_Syntax.vars =
                    (uu___140_8318.FStar_Syntax_Syntax.vars)
                })
         | uu____8319 -> FStar_Pervasives_Native.None)
    | uu____8320 -> failwith "Unexpected number of arguments"  in
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
    let uu____8372 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____8372 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____8417 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8417) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____8477  ->
           fun subst1  ->
             match uu____8477 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____8518,uu____8519)) ->
                      let uu____8578 = b  in
                      (match uu____8578 with
                       | (bv,uu____8586) ->
                           let uu____8587 =
                             let uu____8588 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____8588  in
                           if uu____8587
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____8593 = unembed_binder term1  in
                              match uu____8593 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____8600 =
                                      let uu___141_8601 = bv  in
                                      let uu____8602 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___141_8601.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___141_8601.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____8602
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____8600
                                     in
                                  let b_for_x =
                                    let uu____8606 =
                                      let uu____8613 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____8613)
                                       in
                                    FStar_Syntax_Syntax.NT uu____8606  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___85_8623  ->
                                         match uu___85_8623 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____8624,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____8626;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____8627;_})
                                             ->
                                             let uu____8632 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____8632
                                         | uu____8633 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____8634 -> subst1)) env []
  
let reduce_primops :
  'Auu____8651 'Auu____8652 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8651) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8652 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if Prims.op_Negation (cfg.steps).primops
          then tm
          else
            (let uu____8694 = FStar_Syntax_Util.head_and_args tm  in
             match uu____8694 with
             | (head1,args) ->
                 let uu____8731 =
                   let uu____8732 = FStar_Syntax_Util.un_uinst head1  in
                   uu____8732.FStar_Syntax_Syntax.n  in
                 (match uu____8731 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____8736 = find_prim_step cfg fv  in
                      (match uu____8736 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.strong_reduction_ok ||
                             (Prims.op_Negation cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.arity
                           then
                             (log_primops cfg
                                (fun uu____8758  ->
                                   let uu____8759 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.name
                                      in
                                   let uu____8760 =
                                     FStar_Util.string_of_int l  in
                                   let uu____8767 =
                                     FStar_Util.string_of_int prim_step.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____8759 uu____8760 uu____8767);
                              tm)
                           else
                             (let uu____8769 =
                                if l = prim_step.arity
                                then (args, [])
                                else FStar_List.splitAt prim_step.arity args
                                 in
                              match uu____8769 with
                              | (args_1,args_2) ->
                                  (log_primops cfg
                                     (fun uu____8880  ->
                                        let uu____8881 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____8881);
                                   (let psc =
                                      {
                                        psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        psc_subst =
                                          (fun uu____8884  ->
                                             if
                                               prim_step.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____8886 =
                                      prim_step.interpretation psc args_1  in
                                    match uu____8886 with
                                    | FStar_Pervasives_Native.None  ->
                                        (log_primops cfg
                                           (fun uu____8892  ->
                                              let uu____8893 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____8893);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (log_primops cfg
                                           (fun uu____8899  ->
                                              let uu____8900 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____8901 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____8900 uu____8901);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____8902 ->
                           (log_primops cfg
                              (fun uu____8906  ->
                                 let uu____8907 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____8907);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8911  ->
                            let uu____8912 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8912);
                       (match args with
                        | (a1,uu____8914)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____8931 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.strong ->
                      (log_primops cfg
                         (fun uu____8943  ->
                            let uu____8944 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____8944);
                       (match args with
                        | (t,uu____8946)::(r,uu____8948)::[] ->
                            let uu____8975 =
                              FStar_Syntax_Embeddings.unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____8975 with
                             | FStar_Pervasives_Native.Some rng ->
                                 let uu___142_8979 = t  in
                                 {
                                   FStar_Syntax_Syntax.n =
                                     (uu___142_8979.FStar_Syntax_Syntax.n);
                                   FStar_Syntax_Syntax.pos = rng;
                                   FStar_Syntax_Syntax.vars =
                                     (uu___142_8979.FStar_Syntax_Syntax.vars)
                                 }
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____8982 -> tm))
                  | uu____8991 -> tm))
  
let reduce_equality :
  'Auu____8996 'Auu____8997 .
    cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____8996) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____8997 -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___143_9035 = cfg  in
         {
           steps =
             (let uu___144_9038 = default_steps  in
              {
                beta = (uu___144_9038.beta);
                iota = (uu___144_9038.iota);
                zeta = (uu___144_9038.zeta);
                weak = (uu___144_9038.weak);
                hnf = (uu___144_9038.hnf);
                primops = true;
                no_delta_steps = (uu___144_9038.no_delta_steps);
                unfold_until = (uu___144_9038.unfold_until);
                unfold_only = (uu___144_9038.unfold_only);
                unfold_fully = (uu___144_9038.unfold_fully);
                unfold_attr = (uu___144_9038.unfold_attr);
                unfold_tac = (uu___144_9038.unfold_tac);
                pure_subterms_within_computations =
                  (uu___144_9038.pure_subterms_within_computations);
                simplify = (uu___144_9038.simplify);
                erase_universes = (uu___144_9038.erase_universes);
                allow_unbound_universes =
                  (uu___144_9038.allow_unbound_universes);
                reify_ = (uu___144_9038.reify_);
                compress_uvars = (uu___144_9038.compress_uvars);
                no_full_norm = (uu___144_9038.no_full_norm);
                check_no_uvars = (uu___144_9038.check_no_uvars);
                unmeta = (uu___144_9038.unmeta);
                unascribe = (uu___144_9038.unascribe)
              });
           tcenv = (uu___143_9035.tcenv);
           debug = (uu___143_9035.debug);
           delta_level = (uu___143_9035.delta_level);
           primitive_steps = equality_ops;
           strong = (uu___143_9035.strong);
           memoize_lazy = (uu___143_9035.memoize_lazy);
           normalize_pure_lets = (uu___143_9035.normalize_pure_lets)
         }) tm
  
let is_norm_request :
  'Auu____9042 .
    FStar_Syntax_Syntax.term -> 'Auu____9042 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____9055 =
        let uu____9062 =
          let uu____9063 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9063.FStar_Syntax_Syntax.n  in
        (uu____9062, args)  in
      match uu____9055 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9069::uu____9070::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____9074::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____9079::uu____9080::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____9083 -> false
  
let (tr_norm_step : FStar_Syntax_Embeddings.norm_step -> step Prims.list) =
  fun uu___86_9094  ->
    match uu___86_9094 with
    | FStar_Syntax_Embeddings.Zeta  -> [Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [Weak]
    | FStar_Syntax_Embeddings.HNF  -> [HNF]
    | FStar_Syntax_Embeddings.Primops  -> [Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____9100 =
          let uu____9103 =
            let uu____9104 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldOnly uu____9104  in
          [uu____9103]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____9100
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____9110 =
          let uu____9113 =
            let uu____9114 = FStar_List.map FStar_Ident.lid_of_str names1  in
            UnfoldFully uu____9114  in
          [uu____9113]  in
        (UnfoldUntil FStar_Syntax_Syntax.Delta_constant) :: uu____9110
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [UnfoldUntil FStar_Syntax_Syntax.Delta_constant; UnfoldAttr t]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list -> step Prims.list) =
  fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____9130 .
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.term,'Auu____9130) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (step Prims.list,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun full_norm  ->
    fun args  ->
      let parse_steps s =
        let uu____9172 =
          let uu____9177 =
            FStar_Syntax_Embeddings.e_list
              FStar_Syntax_Embeddings.e_norm_step
             in
          FStar_Syntax_Embeddings.try_unembed uu____9177 s  in
        match uu____9172 with
        | FStar_Pervasives_Native.Some steps ->
            let uu____9193 = tr_norm_steps steps  in
            FStar_Pervasives_Native.Some uu____9193
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
      match args with
      | uu____9210::(tm,uu____9212)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (tm,uu____9241)::[] ->
          let s =
            [Beta;
            Zeta;
            Iota;
            Primops;
            UnfoldUntil FStar_Syntax_Syntax.Delta_constant;
            Reify]  in
          FStar_Pervasives_Native.Some (s, tm)
      | (steps,uu____9262)::uu____9263::(tm,uu____9265)::[] ->
          let add_exclude s z =
            if FStar_List.contains z s then s else (Exclude z) :: s  in
          let uu____9302 =
            let uu____9307 = full_norm steps  in parse_steps uu____9307  in
          (match uu____9302 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some s ->
               let s1 = Beta :: s  in
               let s2 = add_exclude s1 Zeta  in
               let s3 = add_exclude s2 Iota  in
               FStar_Pervasives_Native.Some (s3, tm))
      | uu____9346 -> FStar_Pervasives_Native.None
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___87_9363  ->
    match uu___87_9363 with
    | (App
        (uu____9366,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____9367;
                      FStar_Syntax_Syntax.vars = uu____9368;_},uu____9369,uu____9370))::uu____9371
        -> true
    | uu____9378 -> false
  
let firstn :
  'Auu____9384 .
    Prims.int ->
      'Auu____9384 Prims.list ->
        ('Auu____9384 Prims.list,'Auu____9384 Prims.list)
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
          (uu____9420,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____9421;
                        FStar_Syntax_Syntax.vars = uu____9422;_},uu____9423,uu____9424))::uu____9425
          -> (cfg.steps).reify_
      | uu____9432 -> false
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9616 ->
                   let uu____9641 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9641
               | uu____9642 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          log cfg
            (fun uu____9650  ->
               let uu____9651 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9652 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9653 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9660 =
                 let uu____9661 =
                   let uu____9664 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9664
                    in
                 stack_to_string uu____9661  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____9651 uu____9652 uu____9653 uu____9660);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_constant uu____9687 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_name uu____9688 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_lazy uu____9689 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9690;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant ;
                 FStar_Syntax_Syntax.fv_qual = uu____9691;_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9694;
                 FStar_Syntax_Syntax.fv_delta = uu____9695;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9696;
                 FStar_Syntax_Syntax.fv_delta = uu____9697;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9698);_}
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_quoted uu____9705 ->
               rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation (cfg.steps).no_full_norm) &&
                  (is_norm_request hd1 args))
                 &&
                 (let uu____9741 =
                    FStar_Ident.lid_equals
                      (cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____9741)
               ->
               let cfg' =
                 let uu___145_9743 = cfg  in
                 {
                   steps =
                     (let uu___146_9746 = cfg.steps  in
                      {
                        beta = (uu___146_9746.beta);
                        iota = (uu___146_9746.iota);
                        zeta = (uu___146_9746.zeta);
                        weak = (uu___146_9746.weak);
                        hnf = (uu___146_9746.hnf);
                        primops = (uu___146_9746.primops);
                        no_delta_steps = false;
                        unfold_until = (uu___146_9746.unfold_until);
                        unfold_only = FStar_Pervasives_Native.None;
                        unfold_fully = FStar_Pervasives_Native.None;
                        unfold_attr = (uu___146_9746.unfold_attr);
                        unfold_tac = (uu___146_9746.unfold_tac);
                        pure_subterms_within_computations =
                          (uu___146_9746.pure_subterms_within_computations);
                        simplify = (uu___146_9746.simplify);
                        erase_universes = (uu___146_9746.erase_universes);
                        allow_unbound_universes =
                          (uu___146_9746.allow_unbound_universes);
                        reify_ = (uu___146_9746.reify_);
                        compress_uvars = (uu___146_9746.compress_uvars);
                        no_full_norm = (uu___146_9746.no_full_norm);
                        check_no_uvars = (uu___146_9746.check_no_uvars);
                        unmeta = (uu___146_9746.unmeta);
                        unascribe = (uu___146_9746.unascribe)
                      });
                   tcenv = (uu___145_9743.tcenv);
                   debug = (uu___145_9743.debug);
                   delta_level =
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.Delta_constant];
                   primitive_steps = (uu___145_9743.primitive_steps);
                   strong = (uu___145_9743.strong);
                   memoize_lazy = (uu___145_9743.memoize_lazy);
                   normalize_pure_lets = true
                 }  in
               let uu____9751 = get_norm_request (norm cfg' env []) args  in
               (match uu____9751 with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____9782  ->
                              fun stack1  ->
                                match uu____9782 with
                                | (a,aq) ->
                                    let uu____9794 =
                                      let uu____9795 =
                                        let uu____9802 =
                                          let uu____9803 =
                                            let uu____9834 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____9834, false)  in
                                          Clos uu____9803  in
                                        (uu____9802, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____9795  in
                                    uu____9794 :: stack1) args)
                       in
                    (log cfg
                       (fun uu____9918  ->
                          let uu____9919 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____9919);
                     norm cfg env stack1 hd1)
                | FStar_Pervasives_Native.Some (s,tm) ->
                    let delta_level =
                      let uu____9941 =
                        FStar_All.pipe_right s
                          (FStar_Util.for_some
                             (fun uu___88_9946  ->
                                match uu___88_9946 with
                                | UnfoldUntil uu____9947 -> true
                                | UnfoldOnly uu____9948 -> true
                                | UnfoldFully uu____9951 -> true
                                | uu____9954 -> false))
                         in
                      if uu____9941
                      then
                        [FStar_TypeChecker_Env.Unfold
                           FStar_Syntax_Syntax.Delta_constant]
                      else [FStar_TypeChecker_Env.NoDelta]  in
                    let cfg'1 =
                      let uu___147_9959 = cfg  in
                      let uu____9960 = to_fsteps s  in
                      {
                        steps = uu____9960;
                        tcenv = (uu___147_9959.tcenv);
                        debug = (uu___147_9959.debug);
                        delta_level;
                        primitive_steps = (uu___147_9959.primitive_steps);
                        strong = (uu___147_9959.strong);
                        memoize_lazy = (uu___147_9959.memoize_lazy);
                        normalize_pure_lets = true
                      }  in
                    let stack' =
                      let tail1 = (Cfg cfg) :: stack  in
                      if (cfg.debug).print_normalized
                      then
                        let uu____9969 =
                          let uu____9970 =
                            let uu____9975 = FStar_Util.now ()  in
                            (t1, uu____9975)  in
                          Debug uu____9970  in
                        uu____9969 :: tail1
                      else tail1  in
                    norm cfg'1 env stack' tm)
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____9979 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____9979
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if (cfg.steps).erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____9988 =
                      let uu____9995 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____9995, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____9988  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____10005 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____10005  in
               let uu____10006 =
                 FStar_TypeChecker_Env.qninfo_is_action qninfo  in
               if uu____10006
               then
                 let b = should_reify cfg stack  in
                 (log cfg
                    (fun uu____10012  ->
                       let uu____10013 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10014 = FStar_Util.string_of_bool b  in
                       FStar_Util.print2
                         ">>> For DM4F action %s, should_reify = %s\n"
                         uu____10013 uu____10014);
                  if b
                  then
                    (let uu____10015 = FStar_List.tl stack  in
                     do_unfold_fv cfg env uu____10015 t1 qninfo fv)
                  else rebuild cfg env stack t1)
               else
                 (let should_delta =
                    (let uu____10023 = find_prim_step cfg fv  in
                     FStar_Option.isNone uu____10023) &&
                      (FStar_All.pipe_right cfg.delta_level
                         (FStar_Util.for_some
                            (fun uu___89_10029  ->
                               match uu___89_10029 with
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
                          (let uu____10039 =
                             cases
                               (FStar_Util.for_some
                                  (FStar_Syntax_Util.attr_eq
                                     FStar_Syntax_Util.tac_opaque_attr))
                               false attrs
                              in
                           Prims.op_Negation uu____10039))
                         &&
                         ((match (cfg.steps).unfold_only with
                           | FStar_Pervasives_Native.None  -> true
                           | FStar_Pervasives_Native.Some lids ->
                               FStar_Util.for_some
                                 (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
                            ||
                            (match (attrs, ((cfg.steps).unfold_attr)) with
                             | (FStar_Pervasives_Native.None
                                ,FStar_Pervasives_Native.Some uu____10058) ->
                                 false
                             | (FStar_Pervasives_Native.Some
                                ats,FStar_Pervasives_Native.Some ats') ->
                                 FStar_Util.for_some
                                   (fun at  ->
                                      FStar_Util.for_some
                                        (FStar_Syntax_Util.attr_eq at) ats')
                                   ats
                             | (uu____10093,uu____10094) -> false)))
                     in
                  let uu____10111 =
                    match (cfg.steps).unfold_fully with
                    | FStar_Pervasives_Native.None  -> (should_delta1, false)
                    | FStar_Pervasives_Native.Some lids ->
                        let uu____10127 =
                          FStar_Util.for_some
                            (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                           in
                        if uu____10127
                        then (true, true)
                        else (should_delta1, false)
                     in
                  match uu____10111 with
                  | (should_delta2,fully) ->
                      (log cfg
                         (fun uu____10140  ->
                            let uu____10141 =
                              FStar_Syntax_Print.term_to_string t1  in
                            let uu____10142 =
                              FStar_Range.string_of_range
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let uu____10143 =
                              FStar_Util.string_of_bool should_delta2  in
                            FStar_Util.print3
                              ">>> For %s (%s), should_delta = %s\n"
                              uu____10141 uu____10142 uu____10143);
                       (let cfg1 =
                          if fully
                          then
                            let uu___148_10145 = cfg  in
                            {
                              steps =
                                (let uu___149_10148 = cfg.steps  in
                                 {
                                   beta = (uu___149_10148.beta);
                                   iota = (uu___149_10148.iota);
                                   zeta = (uu___149_10148.zeta);
                                   weak = (uu___149_10148.weak);
                                   hnf = (uu___149_10148.hnf);
                                   primops = (uu___149_10148.primops);
                                   no_delta_steps =
                                     (uu___149_10148.no_delta_steps);
                                   unfold_until =
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Delta_constant);
                                   unfold_only = FStar_Pervasives_Native.None;
                                   unfold_fully =
                                     (uu___149_10148.unfold_fully);
                                   unfold_attr = (uu___149_10148.unfold_attr);
                                   unfold_tac = (uu___149_10148.unfold_tac);
                                   pure_subterms_within_computations =
                                     (uu___149_10148.pure_subterms_within_computations);
                                   simplify = (uu___149_10148.simplify);
                                   erase_universes =
                                     (uu___149_10148.erase_universes);
                                   allow_unbound_universes =
                                     (uu___149_10148.allow_unbound_universes);
                                   reify_ = (uu___149_10148.reify_);
                                   compress_uvars =
                                     (uu___149_10148.compress_uvars);
                                   no_full_norm =
                                     (uu___149_10148.no_full_norm);
                                   check_no_uvars =
                                     (uu___149_10148.check_no_uvars);
                                   unmeta = (uu___149_10148.unmeta);
                                   unascribe = (uu___149_10148.unascribe)
                                 });
                              tcenv = (uu___148_10145.tcenv);
                              debug = (uu___148_10145.debug);
                              delta_level = (uu___148_10145.delta_level);
                              primitive_steps =
                                (uu___148_10145.primitive_steps);
                              strong = (uu___148_10145.strong);
                              memoize_lazy = (uu___148_10145.memoize_lazy);
                              normalize_pure_lets =
                                (uu___148_10145.normalize_pure_lets)
                            }
                          else cfg  in
                        if should_delta2
                        then do_unfold_fv cfg1 env stack t1 qninfo fv
                        else rebuild cfg1 env stack t1)))
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10154 = lookup_bvar env x  in
               (match uu____10154 with
                | Univ uu____10157 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if (Prims.op_Negation fix) || (cfg.steps).zeta
                    then
                      let uu____10206 = FStar_ST.op_Bang r  in
                      (match uu____10206 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (log cfg
                              (fun uu____10324  ->
                                 let uu____10325 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10326 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10325
                                   uu____10326);
                            (let uu____10327 =
                               let uu____10328 =
                                 FStar_Syntax_Subst.compress t'  in
                               uu____10328.FStar_Syntax_Syntax.n  in
                             match uu____10327 with
                             | FStar_Syntax_Syntax.Tm_abs uu____10331 ->
                                 norm cfg env2 stack t'
                             | uu____10348 -> rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10418)::uu____10419 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Match uu____10428)::uu____10429 ->
                    failwith
                      "Ill-typed term: cannot pattern match an abstraction"
                | (Arg (c,uu____10439,uu____10440))::stack_rest ->
                    (match c with
                     | Univ uu____10444 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10453 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (log cfg
                                 (fun uu____10474  ->
                                    let uu____10475 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10475);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (log cfg
                                 (fun uu____10515  ->
                                    let uu____10516 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10516);
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
                       (fun uu____10594  ->
                          let uu____10595 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10595);
                     norm cfg env stack1 t1)
                | (Debug uu____10596)::uu____10597 ->
                    if (cfg.steps).weak
                    then
                      let uu____10604 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10604
                    else
                      (let uu____10606 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10606 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10648  -> dummy :: env1) env)
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
                                          let uu____10685 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10685)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_10690 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_10690.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_10690.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10691 -> lopt  in
                           (log cfg
                              (fun uu____10697  ->
                                 let uu____10698 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10698);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_10707 = cfg  in
                               {
                                 steps = (uu___151_10707.steps);
                                 tcenv = (uu___151_10707.tcenv);
                                 debug = (uu___151_10707.debug);
                                 delta_level = (uu___151_10707.delta_level);
                                 primitive_steps =
                                   (uu___151_10707.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_10707.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_10707.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10718)::uu____10719 ->
                    if (cfg.steps).weak
                    then
                      let uu____10726 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10726
                    else
                      (let uu____10728 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10728 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10770  -> dummy :: env1) env)
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
                                          let uu____10807 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10807)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_10812 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_10812.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_10812.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10813 -> lopt  in
                           (log cfg
                              (fun uu____10819  ->
                                 let uu____10820 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10820);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_10829 = cfg  in
                               {
                                 steps = (uu___151_10829.steps);
                                 tcenv = (uu___151_10829.tcenv);
                                 debug = (uu___151_10829.debug);
                                 delta_level = (uu___151_10829.delta_level);
                                 primitive_steps =
                                   (uu___151_10829.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_10829.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_10829.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____10840)::uu____10841 ->
                    if (cfg.steps).weak
                    then
                      let uu____10852 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10852
                    else
                      (let uu____10854 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10854 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10896  -> dummy :: env1) env)
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
                                          let uu____10933 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10933)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_10938 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_10938.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_10938.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10939 -> lopt  in
                           (log cfg
                              (fun uu____10945  ->
                                 let uu____10946 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10946);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_10955 = cfg  in
                               {
                                 steps = (uu___151_10955.steps);
                                 tcenv = (uu___151_10955.tcenv);
                                 debug = (uu___151_10955.debug);
                                 delta_level = (uu___151_10955.delta_level);
                                 primitive_steps =
                                   (uu___151_10955.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_10955.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_10955.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____10966)::uu____10967 ->
                    if (cfg.steps).weak
                    then
                      let uu____10978 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10978
                    else
                      (let uu____10980 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10980 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11022  -> dummy :: env1) env)
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
                                          let uu____11059 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11059)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11064 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11064.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11064.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11065 -> lopt  in
                           (log cfg
                              (fun uu____11071  ->
                                 let uu____11072 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11072);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11081 = cfg  in
                               {
                                 steps = (uu___151_11081.steps);
                                 tcenv = (uu___151_11081.tcenv);
                                 debug = (uu___151_11081.debug);
                                 delta_level = (uu___151_11081.delta_level);
                                 primitive_steps =
                                   (uu___151_11081.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11081.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11081.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11092)::uu____11093 ->
                    if (cfg.steps).weak
                    then
                      let uu____11108 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11108
                    else
                      (let uu____11110 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11110 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11152  -> dummy :: env1) env)
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
                                          let uu____11189 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11189)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11194 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11194.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11194.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11195 -> lopt  in
                           (log cfg
                              (fun uu____11201  ->
                                 let uu____11202 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11202);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11211 = cfg  in
                               {
                                 steps = (uu___151_11211.steps);
                                 tcenv = (uu___151_11211.tcenv);
                                 debug = (uu___151_11211.debug);
                                 delta_level = (uu___151_11211.delta_level);
                                 primitive_steps =
                                   (uu___151_11211.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11211.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11211.normalize_pure_lets)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if (cfg.steps).weak
                    then
                      let uu____11222 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11222
                    else
                      (let uu____11224 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11224 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11266  -> dummy :: env1) env)
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
                                          let uu____11303 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11303)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___150_11308 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___150_11308.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___150_11308.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11309 -> lopt  in
                           (log cfg
                              (fun uu____11315  ->
                                 let uu____11316 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11316);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___151_11325 = cfg  in
                               {
                                 steps = (uu___151_11325.steps);
                                 tcenv = (uu___151_11325.tcenv);
                                 debug = (uu___151_11325.debug);
                                 delta_level = (uu___151_11325.delta_level);
                                 primitive_steps =
                                   (uu___151_11325.primitive_steps);
                                 strong = true;
                                 memoize_lazy = (uu___151_11325.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___151_11325.normalize_pure_lets)
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
                      (fun uu____11374  ->
                         fun stack1  ->
                           match uu____11374 with
                           | (a,aq) ->
                               let uu____11386 =
                                 let uu____11387 =
                                   let uu____11394 =
                                     let uu____11395 =
                                       let uu____11426 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____11426, false)  in
                                     Clos uu____11395  in
                                   (uu____11394, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____11387  in
                               uu____11386 :: stack1) args)
                  in
               (log cfg
                  (fun uu____11510  ->
                     let uu____11511 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____11511);
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
                             ((let uu___152_11547 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___152_11547.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___152_11547.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____11548 ->
                      let uu____11553 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11553)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____11556 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____11556 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____11587 =
                          let uu____11588 =
                            let uu____11595 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___153_11597 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___153_11597.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___153_11597.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____11595)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____11588  in
                        mk uu____11587 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if (cfg.steps).weak
               then
                 let uu____11616 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____11616
               else
                 (let uu____11618 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____11618 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____11626 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____11650  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____11626 c1  in
                      let t2 =
                        let uu____11672 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____11672 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.steps).unascribe -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____11783)::uu____11784 ->
                    (log cfg
                       (fun uu____11795  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____11796)::uu____11797 ->
                    (log cfg
                       (fun uu____11808  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____11809,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____11810;
                                   FStar_Syntax_Syntax.vars = uu____11811;_},uu____11812,uu____11813))::uu____11814
                    ->
                    (log cfg
                       (fun uu____11823  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____11824)::uu____11825 ->
                    (log cfg
                       (fun uu____11836  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____11837 ->
                    (log cfg
                       (fun uu____11840  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      log cfg
                        (fun uu____11844  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____11861 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____11861
                         | FStar_Util.Inr c ->
                             let uu____11869 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____11869
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____11882 =
                               let uu____11883 =
                                 let uu____11910 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____11910, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11883
                                in
                             mk uu____11882 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____11929 ->
                           let uu____11930 =
                             let uu____11931 =
                               let uu____11932 =
                                 let uu____11959 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____11959, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11932
                                in
                             mk uu____11931 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____11930))))
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
                         let uu____12069 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12069 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___154_12089 = cfg  in
                               let uu____12090 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.tcenv lbunivs
                                  in
                               {
                                 steps = (uu___154_12089.steps);
                                 tcenv = uu____12090;
                                 debug = (uu___154_12089.debug);
                                 delta_level = (uu___154_12089.delta_level);
                                 primitive_steps =
                                   (uu___154_12089.primitive_steps);
                                 strong = (uu___154_12089.strong);
                                 memoize_lazy = (uu___154_12089.memoize_lazy);
                                 normalize_pure_lets =
                                   (uu___154_12089.normalize_pure_lets)
                               }  in
                             let norm1 t2 =
                               let uu____12095 =
                                 let uu____12096 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____12096  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12095
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___155_12099 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___155_12099.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___155_12099.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___155_12099.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___155_12099.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12100 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12100
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12111,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12112;
                               FStar_Syntax_Syntax.lbunivs = uu____12113;
                               FStar_Syntax_Syntax.lbtyp = uu____12114;
                               FStar_Syntax_Syntax.lbeff = uu____12115;
                               FStar_Syntax_Syntax.lbdef = uu____12116;
                               FStar_Syntax_Syntax.lbattrs = uu____12117;
                               FStar_Syntax_Syntax.lbpos = uu____12118;_}::uu____12119),uu____12120)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____12160 =
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
               if uu____12160
               then
                 let binder =
                   let uu____12162 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____12162  in
                 let env1 =
                   let uu____12172 =
                     let uu____12179 =
                       let uu____12180 =
                         let uu____12211 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12211,
                           false)
                          in
                       Clos uu____12180  in
                     ((FStar_Pervasives_Native.Some binder), uu____12179)  in
                   uu____12172 :: env  in
                 (log cfg
                    (fun uu____12304  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if (cfg.steps).weak
                 then
                   (log cfg
                      (fun uu____12308  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12309 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____12309))
                 else
                   (let uu____12311 =
                      let uu____12316 =
                        let uu____12317 =
                          let uu____12318 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____12318
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____12317]  in
                      FStar_Syntax_Subst.open_term uu____12316 body  in
                    match uu____12311 with
                    | (bs,body1) ->
                        (log cfg
                           (fun uu____12327  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____12335 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____12335  in
                            FStar_Util.Inl
                              (let uu___156_12345 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___156_12345.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___156_12345.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          log cfg
                            (fun uu____12348  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___157_12350 = lb  in
                             let uu____12351 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___157_12350.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___157_12350.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____12351;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___157_12350.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___157_12350.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12386  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___158_12409 = cfg  in
                             {
                               steps = (uu___158_12409.steps);
                               tcenv = (uu___158_12409.tcenv);
                               debug = (uu___158_12409.debug);
                               delta_level = (uu___158_12409.delta_level);
                               primitive_steps =
                                 (uu___158_12409.primitive_steps);
                               strong = true;
                               memoize_lazy = (uu___158_12409.memoize_lazy);
                               normalize_pure_lets =
                                 (uu___158_12409.normalize_pure_lets)
                             }  in
                           log cfg1
                             (fun uu____12412  ->
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
               let uu____12429 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____12429 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____12465 =
                               let uu___159_12466 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___159_12466.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___159_12466.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____12465  in
                           let uu____12467 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____12467 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____12493 =
                                   FStar_List.map (fun uu____12509  -> dummy)
                                     lbs1
                                    in
                                 let uu____12510 =
                                   let uu____12519 =
                                     FStar_List.map
                                       (fun uu____12539  -> dummy) xs1
                                      in
                                   FStar_List.append uu____12519 env  in
                                 FStar_List.append uu____12493 uu____12510
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12563 =
                                       let uu___160_12564 = rc  in
                                       let uu____12565 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___160_12564.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12565;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___160_12564.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____12563
                                 | uu____12572 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___161_12576 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___161_12576.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___161_12576.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___161_12576.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___161_12576.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____12586 =
                        FStar_List.map (fun uu____12602  -> dummy) lbs2  in
                      FStar_List.append uu____12586 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____12610 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____12610 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___162_12626 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___162_12626.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___162_12626.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation (cfg.steps).zeta ->
               let uu____12653 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____12653
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____12672 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____12748  ->
                        match uu____12748 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___163_12869 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___163_12869.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___163_12869.FStar_Syntax_Syntax.sort)
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
               (match uu____12672 with
                | (rec_env,memos,uu____13082) ->
                    let uu____13135 =
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
                             let uu____13446 =
                               let uu____13453 =
                                 let uu____13454 =
                                   let uu____13485 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____13485, false)
                                    in
                                 Clos uu____13454  in
                               (FStar_Pervasives_Native.None, uu____13453)
                                in
                             uu____13446 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (log cfg
                  (fun uu____13595  ->
                     let uu____13596 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____13596);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____13618 ->
                     if (cfg.steps).unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____13620::uu____13621 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____13626) ->
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
                             | uu____13649 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____13663 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____13663
                              | uu____13674 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____13678 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____13704 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____13722 ->
                    if (cfg.steps).check_no_uvars
                    then
                      let uu____13739 =
                        let uu____13740 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____13741 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____13740 uu____13741
                         in
                      failwith uu____13739
                    else rebuild cfg env stack t2
                | uu____13743 -> norm cfg env stack t2))

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
                let uu____13753 = FStar_Syntax_Syntax.range_of_fv f  in
                FStar_TypeChecker_Env.set_range cfg.tcenv uu____13753  in
              let uu____13754 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____13754 with
              | FStar_Pervasives_Native.None  ->
                  (log cfg
                     (fun uu____13767  ->
                        FStar_Util.print "Tm_fvar case 2\n" []);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (log cfg
                     (fun uu____13778  ->
                        let uu____13779 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____13780 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 ">>> Unfolded %s to %s\n"
                          uu____13779 uu____13780);
                   (let t1 =
                      if
                        ((cfg.steps).unfold_until =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Delta_constant))
                          && (Prims.op_Negation (cfg.steps).unfold_tac)
                      then t
                      else
                        (let uu____13785 =
                           FStar_Ident.range_of_lid
                             (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            in
                         FStar_Syntax_Subst.set_use_range uu____13785 t)
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____13794))::stack1 ->
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
                      | uu____13849 when
                          (cfg.steps).erase_universes ||
                            (cfg.steps).allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____13852 ->
                          let uu____13855 =
                            let uu____13856 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____13856
                             in
                          failwith uu____13855
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
                  let uu___164_13880 = cfg  in
                  let uu____13881 =
                    FStar_List.fold_right fstep_add_one new_steps cfg.steps
                     in
                  {
                    steps = uu____13881;
                    tcenv = (uu___164_13880.tcenv);
                    debug = (uu___164_13880.debug);
                    delta_level =
                      [FStar_TypeChecker_Env.Inlining;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    primitive_steps = (uu___164_13880.primitive_steps);
                    strong = (uu___164_13880.strong);
                    memoize_lazy = (uu___164_13880.memoize_lazy);
                    normalize_pure_lets =
                      (uu___164_13880.normalize_pure_lets)
                  }
                else
                  (let uu___165_13883 = cfg  in
                   {
                     steps =
                       (let uu___166_13886 = cfg.steps  in
                        {
                          beta = (uu___166_13886.beta);
                          iota = (uu___166_13886.iota);
                          zeta = false;
                          weak = (uu___166_13886.weak);
                          hnf = (uu___166_13886.hnf);
                          primops = (uu___166_13886.primops);
                          no_delta_steps = (uu___166_13886.no_delta_steps);
                          unfold_until = (uu___166_13886.unfold_until);
                          unfold_only = (uu___166_13886.unfold_only);
                          unfold_fully = (uu___166_13886.unfold_fully);
                          unfold_attr = (uu___166_13886.unfold_attr);
                          unfold_tac = (uu___166_13886.unfold_tac);
                          pure_subterms_within_computations =
                            (uu___166_13886.pure_subterms_within_computations);
                          simplify = (uu___166_13886.simplify);
                          erase_universes = (uu___166_13886.erase_universes);
                          allow_unbound_universes =
                            (uu___166_13886.allow_unbound_universes);
                          reify_ = (uu___166_13886.reify_);
                          compress_uvars = (uu___166_13886.compress_uvars);
                          no_full_norm = (uu___166_13886.no_full_norm);
                          check_no_uvars = (uu___166_13886.check_no_uvars);
                          unmeta = (uu___166_13886.unmeta);
                          unascribe = (uu___166_13886.unascribe)
                        });
                     tcenv = (uu___165_13883.tcenv);
                     debug = (uu___165_13883.debug);
                     delta_level = (uu___165_13883.delta_level);
                     primitive_steps = (uu___165_13883.primitive_steps);
                     strong = (uu___165_13883.strong);
                     memoize_lazy = (uu___165_13883.memoize_lazy);
                     normalize_pure_lets =
                       (uu___165_13883.normalize_pure_lets)
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
                  (fun uu____13916  ->
                     let uu____13917 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____13918 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____13917
                       uu____13918);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____13920 =
                   let uu____13921 = FStar_Syntax_Subst.compress head3  in
                   uu____13921.FStar_Syntax_Syntax.n  in
                 match uu____13920 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____13939 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____13939
                        in
                     let uu____13940 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____13940 with
                      | (uu____13941,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____13947 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____13955 =
                                   let uu____13956 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____13956.FStar_Syntax_Syntax.n  in
                                 match uu____13955 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____13962,uu____13963))
                                     ->
                                     let uu____13972 =
                                       let uu____13973 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____13973.FStar_Syntax_Syntax.n  in
                                     (match uu____13972 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____13979,msrc,uu____13981))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____13990 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____13990
                                      | uu____13991 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____13992 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____13993 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____13993 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___167_13998 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___167_13998.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___167_13998.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___167_13998.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___167_13998.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___167_13998.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____13999 = FStar_List.tl stack  in
                                    let uu____14000 =
                                      let uu____14001 =
                                        let uu____14004 =
                                          let uu____14005 =
                                            let uu____14018 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____14018)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____14005
                                           in
                                        FStar_Syntax_Syntax.mk uu____14004
                                         in
                                      uu____14001
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____13999 uu____14000
                                | FStar_Pervasives_Native.None  ->
                                    let uu____14034 =
                                      let uu____14035 = is_return body  in
                                      match uu____14035 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____14039;
                                            FStar_Syntax_Syntax.vars =
                                              uu____14040;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____14045 -> false  in
                                    if uu____14034
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
                                         let uu____14068 =
                                           let uu____14071 =
                                             let uu____14072 =
                                               let uu____14089 =
                                                 let uu____14092 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____14092]  in
                                               (uu____14089, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____14072
                                              in
                                           FStar_Syntax_Syntax.mk uu____14071
                                            in
                                         uu____14068
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____14108 =
                                           let uu____14109 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____14109.FStar_Syntax_Syntax.n
                                            in
                                         match uu____14108 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____14115::uu____14116::[])
                                             ->
                                             let uu____14123 =
                                               let uu____14126 =
                                                 let uu____14127 =
                                                   let uu____14134 =
                                                     let uu____14137 =
                                                       let uu____14138 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.tcenv
                                                         uu____14138
                                                        in
                                                     let uu____14139 =
                                                       let uu____14142 =
                                                         let uu____14143 =
                                                           close1 t  in
                                                         (cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.tcenv
                                                           uu____14143
                                                          in
                                                       [uu____14142]  in
                                                     uu____14137 ::
                                                       uu____14139
                                                      in
                                                   (bind1, uu____14134)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____14127
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____14126
                                                in
                                             uu____14123
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____14151 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____14157 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____14157
                                         then
                                           let uu____14160 =
                                             let uu____14161 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____14161
                                              in
                                           let uu____14162 =
                                             let uu____14165 =
                                               let uu____14166 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____14166
                                                in
                                             [uu____14165]  in
                                           uu____14160 :: uu____14162
                                         else []  in
                                       let reified =
                                         let uu____14171 =
                                           let uu____14174 =
                                             let uu____14175 =
                                               let uu____14190 =
                                                 let uu____14193 =
                                                   let uu____14196 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____14197 =
                                                     let uu____14200 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____14200]  in
                                                   uu____14196 :: uu____14197
                                                    in
                                                 let uu____14201 =
                                                   let uu____14204 =
                                                     let uu____14207 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____14208 =
                                                       let uu____14211 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____14212 =
                                                         let uu____14215 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____14216 =
                                                           let uu____14219 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____14219]  in
                                                         uu____14215 ::
                                                           uu____14216
                                                          in
                                                       uu____14211 ::
                                                         uu____14212
                                                        in
                                                     uu____14207 ::
                                                       uu____14208
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____14204
                                                    in
                                                 FStar_List.append
                                                   uu____14193 uu____14201
                                                  in
                                               (bind_inst, uu____14190)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____14175
                                              in
                                           FStar_Syntax_Syntax.mk uu____14174
                                            in
                                         uu____14171
                                           FStar_Pervasives_Native.None rng
                                          in
                                       log cfg
                                         (fun uu____14231  ->
                                            let uu____14232 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____14233 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____14232 uu____14233);
                                       (let uu____14234 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____14234 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____14258 =
                         FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m  in
                       FStar_TypeChecker_Env.get_effect_decl cfg.tcenv
                         uu____14258
                        in
                     let uu____14259 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____14259 with
                      | (uu____14260,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____14295 =
                                  let uu____14296 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____14296.FStar_Syntax_Syntax.n  in
                                match uu____14295 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____14302) -> t2
                                | uu____14307 -> head4  in
                              let uu____14308 =
                                let uu____14309 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____14309.FStar_Syntax_Syntax.n  in
                              match uu____14308 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____14315 -> FStar_Pervasives_Native.None
                               in
                            let uu____14316 = maybe_extract_fv head4  in
                            match uu____14316 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____14326 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action cfg.tcenv
                                  uu____14326
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____14331 = maybe_extract_fv head5
                                     in
                                  match uu____14331 with
                                  | FStar_Pervasives_Native.Some uu____14336
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____14337 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____14342 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____14357 =
                              match uu____14357 with
                              | (e,q) ->
                                  let uu____14364 =
                                    let uu____14365 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14365.FStar_Syntax_Syntax.n  in
                                  (match uu____14364 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____14380 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____14380
                                   | uu____14381 -> false)
                               in
                            let uu____14382 =
                              let uu____14383 =
                                let uu____14390 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____14390 :: args  in
                              FStar_Util.for_some is_arg_impure uu____14383
                               in
                            if uu____14382
                            then
                              let uu____14395 =
                                let uu____14396 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____14396
                                 in
                              failwith uu____14395
                            else ());
                           (let uu____14398 = maybe_unfold_action head_app
                               in
                            match uu____14398 with
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
                                   (fun uu____14439  ->
                                      let uu____14440 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____14441 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____14440 uu____14441);
                                 (let uu____14442 = FStar_List.tl stack  in
                                  norm cfg env uu____14442 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____14444) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____14468 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____14468  in
                     (log cfg
                        (fun uu____14472  ->
                           let uu____14473 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____14473);
                      (let uu____14474 = FStar_List.tl stack  in
                       norm cfg env uu____14474 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____14595  ->
                               match uu____14595 with
                               | (pat,wopt,tm) ->
                                   let uu____14643 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____14643)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____14675 = FStar_List.tl stack  in
                     norm cfg env uu____14675 tm
                 | uu____14676 -> fallback ())

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
              (fun uu____14690  ->
                 let uu____14691 = FStar_Ident.string_of_lid msrc  in
                 let uu____14692 = FStar_Ident.string_of_lid mtgt  in
                 let uu____14693 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____14691
                   uu____14692 uu____14693);
            (let uu____14694 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____14694
             then
               let ed =
                 let uu____14696 =
                   FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt  in
                 FStar_TypeChecker_Env.get_effect_decl env uu____14696  in
               let uu____14697 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____14697 with
               | (uu____14698,return_repr) ->
                   let return_inst =
                     let uu____14707 =
                       let uu____14708 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____14708.FStar_Syntax_Syntax.n  in
                     match uu____14707 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____14714::[]) ->
                         let uu____14721 =
                           let uu____14724 =
                             let uu____14725 =
                               let uu____14732 =
                                 let uu____14735 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____14735]  in
                               (return_tm, uu____14732)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____14725  in
                           FStar_Syntax_Syntax.mk uu____14724  in
                         uu____14721 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____14743 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____14746 =
                     let uu____14749 =
                       let uu____14750 =
                         let uu____14765 =
                           let uu____14768 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____14769 =
                             let uu____14772 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____14772]  in
                           uu____14768 :: uu____14769  in
                         (return_inst, uu____14765)  in
                       FStar_Syntax_Syntax.Tm_app uu____14750  in
                     FStar_Syntax_Syntax.mk uu____14749  in
                   uu____14746 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____14781 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____14781 with
                | FStar_Pervasives_Native.None  ->
                    let uu____14784 =
                      let uu____14785 = FStar_Ident.text_of_lid msrc  in
                      let uu____14786 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____14785 uu____14786
                       in
                    failwith uu____14784
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14787;
                      FStar_TypeChecker_Env.mtarget = uu____14788;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14789;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____14804 =
                      let uu____14805 = FStar_Ident.text_of_lid msrc  in
                      let uu____14806 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____14805 uu____14806
                       in
                    failwith uu____14804
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14807;
                      FStar_TypeChecker_Env.mtarget = uu____14808;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14809;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____14833 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____14834 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____14833 t FStar_Syntax_Syntax.tun uu____14834))

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
                (fun uu____14890  ->
                   match uu____14890 with
                   | (a,imp) ->
                       let uu____14901 = norm cfg env [] a  in
                       (uu____14901, imp))))

and (norm_comp :
  cfg -> env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        log cfg
          (fun uu____14909  ->
             let uu____14910 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____14911 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____14910 uu____14911);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14935 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                     uu____14935
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___168_14938 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___168_14938.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___168_14938.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14958 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_43  -> FStar_Pervasives_Native.Some _0_43)
                     uu____14958
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___169_14961 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___169_14961.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___169_14961.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____14994  ->
                      match uu____14994 with
                      | (a,i) ->
                          let uu____15005 = norm cfg env [] a  in
                          (uu____15005, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___90_15023  ->
                       match uu___90_15023 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____15027 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____15027
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___170_15035 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___171_15038 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___171_15038.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___170_15035.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___170_15035.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  cfg -> env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun cfg  ->
    fun env  ->
      fun uu____15041  ->
        match uu____15041 with
        | (x,imp) ->
            let uu____15044 =
              let uu___172_15045 = x  in
              let uu____15046 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___172_15045.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___172_15045.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15046
              }  in
            (uu____15044, imp)

and (norm_binders :
  cfg -> env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders) =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____15052 =
          FStar_List.fold_left
            (fun uu____15070  ->
               fun b  ->
                 match uu____15070 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____15052 with | (nbs,uu____15110) -> FStar_List.rev nbs

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
            let uu____15126 =
              let uu___173_15127 = rc  in
              let uu____15128 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___173_15127.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____15128;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___173_15127.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____15126
        | uu____15135 -> lopt

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
            (let uu____15156 = FStar_Syntax_Print.term_to_string tm  in
             let uu____15157 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if (cfg.steps).simplify then "" else "NOT ") uu____15156
               uu____15157)
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
          let uu____15177 =
            FStar_All.pipe_left Prims.op_Negation (cfg.steps).simplify  in
          if uu____15177
          then tm1
          else
            (let w t =
               let uu___174_15189 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___174_15189.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___174_15189.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____15198 =
                 let uu____15199 = FStar_Syntax_Util.unmeta t  in
                 uu____15199.FStar_Syntax_Syntax.n  in
               match uu____15198 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____15206 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____15251)::args1,(bv,uu____15254)::bs1) ->
                   let uu____15288 =
                     let uu____15289 = FStar_Syntax_Subst.compress t  in
                     uu____15289.FStar_Syntax_Syntax.n  in
                   (match uu____15288 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____15293 -> false)
               | ([],[]) -> true
               | (uu____15314,uu____15315) -> false  in
             let is_applied bs t =
               let uu____15351 = FStar_Syntax_Util.head_and_args' t  in
               match uu____15351 with
               | (hd1,args) ->
                   let uu____15384 =
                     let uu____15385 = FStar_Syntax_Subst.compress hd1  in
                     uu____15385.FStar_Syntax_Syntax.n  in
                   (match uu____15384 with
                    | FStar_Syntax_Syntax.Tm_name bv when
                        args_are_binders args bs ->
                        FStar_Pervasives_Native.Some bv
                    | uu____15391 -> FStar_Pervasives_Native.None)
                in
             let is_applied_maybe_squashed bs t =
               let uu____15403 = FStar_Syntax_Util.is_squash t  in
               match uu____15403 with
               | FStar_Pervasives_Native.Some (uu____15414,t') ->
                   is_applied bs t'
               | uu____15426 ->
                   let uu____15435 = FStar_Syntax_Util.is_auto_squash t  in
                   (match uu____15435 with
                    | FStar_Pervasives_Native.Some (uu____15446,t') ->
                        is_applied bs t'
                    | uu____15458 -> is_applied bs t)
                in
             let is_quantified_const phi =
               let uu____15475 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15475 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____15482)::(q,uu____15484)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   let uu____15519 =
                     FStar_Syntax_Util.destruct_typ_as_formula p  in
                   (match uu____15519 with
                    | FStar_Pervasives_Native.None  ->
                        let uu____15524 =
                          let uu____15525 = FStar_Syntax_Subst.compress p  in
                          uu____15525.FStar_Syntax_Syntax.n  in
                        (match uu____15524 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15531 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_true)] q
                                in
                             FStar_Pervasives_Native.Some uu____15531
                         | uu____15532 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Util.BaseConn
                        (lid1,(p1,uu____15535)::[])) when
                        FStar_Ident.lid_equals lid1
                          FStar_Parser_Const.not_lid
                        ->
                        let uu____15560 =
                          let uu____15561 = FStar_Syntax_Subst.compress p1
                             in
                          uu____15561.FStar_Syntax_Syntax.n  in
                        (match uu____15560 with
                         | FStar_Syntax_Syntax.Tm_bvar bv ->
                             let uu____15567 =
                               FStar_Syntax_Subst.subst
                                 [FStar_Syntax_Syntax.NT
                                    (bv, FStar_Syntax_Util.t_false)] q
                                in
                             FStar_Pervasives_Native.Some uu____15567
                         | uu____15568 -> FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                        (bs,pats,phi1)) ->
                        let uu____15572 =
                          FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                        (match uu____15572 with
                         | FStar_Pervasives_Native.None  ->
                             let uu____15577 =
                               is_applied_maybe_squashed bs phi1  in
                             (match uu____15577 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ftrue =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_true
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____15584 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ftrue)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____15584
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Pervasives_Native.None)
                         | FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.BaseConn
                             (lid1,(p1,uu____15587)::[])) when
                             FStar_Ident.lid_equals lid1
                               FStar_Parser_Const.not_lid
                             ->
                             let uu____15612 =
                               is_applied_maybe_squashed bs p1  in
                             (match uu____15612 with
                              | FStar_Pervasives_Native.Some bv ->
                                  let ffalse =
                                    FStar_Syntax_Util.abs bs
                                      FStar_Syntax_Util.t_false
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.residual_tot
                                            FStar_Syntax_Util.ktype0))
                                     in
                                  let uu____15619 =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT (bv, ffalse)] q
                                     in
                                  FStar_Pervasives_Native.Some uu____15619
                              | uu____15620 -> FStar_Pervasives_Native.None)
                         | uu____15623 -> FStar_Pervasives_Native.None)
                    | uu____15626 -> FStar_Pervasives_Native.None)
               | uu____15629 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____15640 =
                 let uu____15641 = FStar_Syntax_Subst.compress phi  in
                 uu____15641.FStar_Syntax_Syntax.n  in
               match uu____15640 with
               | FStar_Syntax_Syntax.Tm_match (uu____15646,br::brs) ->
                   let uu____15713 = br  in
                   (match uu____15713 with
                    | (uu____15730,uu____15731,e) ->
                        let r =
                          let uu____15752 = simp_t e  in
                          match uu____15752 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____15758 =
                                FStar_List.for_all
                                  (fun uu____15776  ->
                                     match uu____15776 with
                                     | (uu____15789,uu____15790,e') ->
                                         let uu____15804 = simp_t e'  in
                                         uu____15804 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____15758
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____15812 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____15817 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____15817
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____15838 =
                 match uu____15838 with
                 | (t1,q) ->
                     let uu____15851 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____15851 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____15879 -> (t1, q))
                  in
               let uu____15888 = FStar_Syntax_Util.head_and_args t  in
               match uu____15888 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____15950 =
                 let uu____15951 = FStar_Syntax_Util.unmeta ty  in
                 uu____15951.FStar_Syntax_Syntax.n  in
               match uu____15950 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____15955) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____15960,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____15980 -> false  in
             let simplify1 arg =
               let uu____16003 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____16003, arg)  in
             let uu____16012 = is_quantified_const tm1  in
             match uu____16012 with
             | FStar_Pervasives_Native.Some tm2 ->
                 let uu____16016 = norm cfg env [] tm2  in
                 maybe_simplify_aux cfg env stack uu____16016
             | FStar_Pervasives_Native.None  ->
                 let uu____16017 =
                   let uu____16018 = FStar_Syntax_Subst.compress tm1  in
                   uu____16018.FStar_Syntax_Syntax.n  in
                 (match uu____16017 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____16022;
                              FStar_Syntax_Syntax.vars = uu____16023;_},uu____16024);
                         FStar_Syntax_Syntax.pos = uu____16025;
                         FStar_Syntax_Syntax.vars = uu____16026;_},args)
                      ->
                      let uu____16052 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____16052
                      then
                        let uu____16053 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____16053 with
                         | (FStar_Pervasives_Native.Some (true ),uu____16100)::
                             (uu____16101,(arg,uu____16103))::[] ->
                             maybe_auto_squash arg
                         | (uu____16152,(arg,uu____16154))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____16155)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____16204)::uu____16205::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16256::(FStar_Pervasives_Native.Some (false
                                         ),uu____16257)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____16308 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16322 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____16322
                         then
                           let uu____16323 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____16323 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____16370)::uu____16371::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16422::(FStar_Pervasives_Native.Some (true
                                           ),uu____16423)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____16474)::(uu____16475,(arg,uu____16477))::[]
                               -> maybe_auto_squash arg
                           | (uu____16526,(arg,uu____16528))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____16529)::[]
                               -> maybe_auto_squash arg
                           | uu____16578 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____16592 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____16592
                            then
                              let uu____16593 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____16593 with
                              | uu____16640::(FStar_Pervasives_Native.Some
                                              (true ),uu____16641)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____16692)::uu____16693::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____16744)::(uu____16745,(arg,uu____16747))::[]
                                  -> maybe_auto_squash arg
                              | (uu____16796,(p,uu____16798))::(uu____16799,
                                                                (q,uu____16801))::[]
                                  ->
                                  let uu____16848 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____16848
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____16850 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____16864 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____16864
                               then
                                 let uu____16865 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____16865 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16912)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16913)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16964)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16965)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17016)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17017)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17068)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17069)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____17120,(arg,uu____17122))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____17123)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17172)::(uu____17173,(arg,uu____17175))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____17224,(arg,uu____17226))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____17227)::[]
                                     ->
                                     let uu____17276 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17276
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17277)::(uu____17278,(arg,uu____17280))::[]
                                     ->
                                     let uu____17329 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17329
                                 | (uu____17330,(p,uu____17332))::(uu____17333,
                                                                   (q,uu____17335))::[]
                                     ->
                                     let uu____17382 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____17382
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17384 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17398 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____17398
                                  then
                                    let uu____17399 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____17399 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____17446)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____17477)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17508 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17522 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____17522
                                     then
                                       match args with
                                       | (t,uu____17524)::[] ->
                                           let uu____17541 =
                                             let uu____17542 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17542.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17541 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17545::[],body,uu____17547)
                                                ->
                                                let uu____17574 = simp_t body
                                                   in
                                                (match uu____17574 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____17577 -> tm1)
                                            | uu____17580 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____17582))::(t,uu____17584)::[]
                                           ->
                                           let uu____17623 =
                                             let uu____17624 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17624.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17623 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17627::[],body,uu____17629)
                                                ->
                                                let uu____17656 = simp_t body
                                                   in
                                                (match uu____17656 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____17659 -> tm1)
                                            | uu____17662 -> tm1)
                                       | uu____17663 -> tm1
                                     else
                                       (let uu____17673 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____17673
                                        then
                                          match args with
                                          | (t,uu____17675)::[] ->
                                              let uu____17692 =
                                                let uu____17693 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17693.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17692 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17696::[],body,uu____17698)
                                                   ->
                                                   let uu____17725 =
                                                     simp_t body  in
                                                   (match uu____17725 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____17728 -> tm1)
                                               | uu____17731 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____17733))::(t,uu____17735)::[]
                                              ->
                                              let uu____17774 =
                                                let uu____17775 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17775.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17774 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17778::[],body,uu____17780)
                                                   ->
                                                   let uu____17807 =
                                                     simp_t body  in
                                                   (match uu____17807 with
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
                                                    | uu____17810 -> tm1)
                                               | uu____17813 -> tm1)
                                          | uu____17814 -> tm1
                                        else
                                          (let uu____17824 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____17824
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17825;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17826;_},uu____17827)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17844;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17845;_},uu____17846)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____17863 -> tm1
                                           else
                                             (let uu____17873 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____17873 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____17893 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____17903;
                         FStar_Syntax_Syntax.vars = uu____17904;_},args)
                      ->
                      let uu____17926 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____17926
                      then
                        let uu____17927 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____17927 with
                         | (FStar_Pervasives_Native.Some (true ),uu____17974)::
                             (uu____17975,(arg,uu____17977))::[] ->
                             maybe_auto_squash arg
                         | (uu____18026,(arg,uu____18028))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18029)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18078)::uu____18079::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18130::(FStar_Pervasives_Native.Some (false
                                         ),uu____18131)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18182 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18196 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18196
                         then
                           let uu____18197 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18197 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18244)::uu____18245::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18296::(FStar_Pervasives_Native.Some (true
                                           ),uu____18297)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18348)::(uu____18349,(arg,uu____18351))::[]
                               -> maybe_auto_squash arg
                           | (uu____18400,(arg,uu____18402))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18403)::[]
                               -> maybe_auto_squash arg
                           | uu____18452 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18466 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18466
                            then
                              let uu____18467 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18467 with
                              | uu____18514::(FStar_Pervasives_Native.Some
                                              (true ),uu____18515)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18566)::uu____18567::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18618)::(uu____18619,(arg,uu____18621))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18670,(p,uu____18672))::(uu____18673,
                                                                (q,uu____18675))::[]
                                  ->
                                  let uu____18722 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____18722
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18724 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18738 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____18738
                               then
                                 let uu____18739 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____18739 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18786)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18787)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18838)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18839)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18890)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18891)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18942)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18943)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____18994,(arg,uu____18996))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____18997)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19046)::(uu____19047,(arg,uu____19049))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19098,(arg,uu____19100))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19101)::[]
                                     ->
                                     let uu____19150 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19150
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19151)::(uu____19152,(arg,uu____19154))::[]
                                     ->
                                     let uu____19203 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19203
                                 | (uu____19204,(p,uu____19206))::(uu____19207,
                                                                   (q,uu____19209))::[]
                                     ->
                                     let uu____19256 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19256
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19258 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19272 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19272
                                  then
                                    let uu____19273 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19273 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19320)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19351)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19382 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19396 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19396
                                     then
                                       match args with
                                       | (t,uu____19398)::[] ->
                                           let uu____19415 =
                                             let uu____19416 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19416.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19415 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19419::[],body,uu____19421)
                                                ->
                                                let uu____19448 = simp_t body
                                                   in
                                                (match uu____19448 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19451 -> tm1)
                                            | uu____19454 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19456))::(t,uu____19458)::[]
                                           ->
                                           let uu____19497 =
                                             let uu____19498 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19498.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19497 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19501::[],body,uu____19503)
                                                ->
                                                let uu____19530 = simp_t body
                                                   in
                                                (match uu____19530 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19533 -> tm1)
                                            | uu____19536 -> tm1)
                                       | uu____19537 -> tm1
                                     else
                                       (let uu____19547 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____19547
                                        then
                                          match args with
                                          | (t,uu____19549)::[] ->
                                              let uu____19566 =
                                                let uu____19567 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19567.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19566 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19570::[],body,uu____19572)
                                                   ->
                                                   let uu____19599 =
                                                     simp_t body  in
                                                   (match uu____19599 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____19602 -> tm1)
                                               | uu____19605 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____19607))::(t,uu____19609)::[]
                                              ->
                                              let uu____19648 =
                                                let uu____19649 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19649.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19648 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19652::[],body,uu____19654)
                                                   ->
                                                   let uu____19681 =
                                                     simp_t body  in
                                                   (match uu____19681 with
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
                                                    | uu____19684 -> tm1)
                                               | uu____19687 -> tm1)
                                          | uu____19688 -> tm1
                                        else
                                          (let uu____19698 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____19698
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19699;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19700;_},uu____19701)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19718;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19719;_},uu____19720)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____19737 -> tm1
                                           else
                                             (let uu____19747 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____19747 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____19767 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____19782 = simp_t t  in
                      (match uu____19782 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____19785 ->
                      let uu____19808 = is_const_match tm1  in
                      (match uu____19808 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____19811 -> tm1))

and (rebuild :
  cfg -> env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          log cfg
            (fun uu____19822  ->
               let uu____19823 = FStar_Syntax_Print.tag_of_term t  in
               let uu____19824 = FStar_Syntax_Print.term_to_string t  in
               let uu____19825 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____19832 =
                 let uu____19833 =
                   let uu____19836 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____19836
                    in
                 stack_to_string uu____19833  in
               FStar_Util.print4
                 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                 uu____19823 uu____19824 uu____19825 uu____19832);
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if (cfg.debug).print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____19867 =
                     let uu____19868 =
                       let uu____19869 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____19869  in
                     FStar_Util.string_of_int uu____19868  in
                   let uu____19874 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____19875 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____19867 uu____19874 uu____19875)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                log cfg
                  (fun uu____19929  ->
                     let uu____19930 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____19930);
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
               let uu____19966 =
                 let uu___175_19967 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___175_19967.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___175_19967.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____19966
           | (Arg (Univ uu____19968,uu____19969,uu____19970))::uu____19971 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____19974,uu____19975))::uu____19976 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____19991,uu____19992),aq,r))::stack1
               when
               let uu____20042 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____20042 ->
               let t2 =
                 let uu____20046 =
                   let uu____20047 =
                     let uu____20048 = closure_as_term cfg env_arg tm  in
                     (uu____20048, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____20047  in
                 uu____20046 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____20054),aq,r))::stack1 ->
               (log cfg
                  (fun uu____20107  ->
                     let uu____20108 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____20108);
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
                  (let uu____20118 = FStar_ST.op_Bang m  in
                   match uu____20118 with
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
                   | FStar_Pervasives_Native.Some (uu____20255,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____20302 =
                 log cfg
                   (fun uu____20306  ->
                      let uu____20307 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____20307);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____20311 =
                 let uu____20312 = FStar_Syntax_Subst.compress t1  in
                 uu____20312.FStar_Syntax_Syntax.n  in
               (match uu____20311 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____20339 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____20339  in
                    (log cfg
                       (fun uu____20343  ->
                          let uu____20344 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____20344);
                     (let uu____20345 = FStar_List.tl stack  in
                      norm cfg env1 uu____20345 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____20346);
                       FStar_Syntax_Syntax.pos = uu____20347;
                       FStar_Syntax_Syntax.vars = uu____20348;_},(e,uu____20350)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____20379 when
                    (cfg.steps).primops ->
                    let uu____20394 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____20394 with
                     | (hd1,args) ->
                         let uu____20431 =
                           let uu____20432 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____20432.FStar_Syntax_Syntax.n  in
                         (match uu____20431 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____20436 = find_prim_step cfg fv  in
                              (match uu____20436 with
                               | FStar_Pervasives_Native.Some
                                   { name = uu____20439; arity = uu____20440;
                                     auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     strong_reduction_ok = uu____20442;
                                     requires_binder_substitution =
                                       uu____20443;
                                     interpretation = uu____20444;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____20457 -> fallback " (3)" ())
                          | uu____20460 -> fallback " (4)" ()))
                | uu____20461 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env1,branches,r))::stack1 ->
               (log cfg
                  (fun uu____20481  ->
                     let uu____20482 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____20482);
                (let scrutinee = t1  in
                 let norm_and_rebuild_match uu____20487 =
                   log cfg
                     (fun uu____20492  ->
                        let uu____20493 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____20494 =
                          let uu____20495 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____20512  ->
                                    match uu____20512 with
                                    | (p,uu____20522,uu____20523) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____20495
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____20493 uu____20494);
                   (let whnf = (cfg.steps).weak || (cfg.steps).hnf  in
                    let cfg_exclude_iota_zeta =
                      let new_delta =
                        FStar_All.pipe_right cfg.delta_level
                          (FStar_List.filter
                             (fun uu___91_20540  ->
                                match uu___91_20540 with
                                | FStar_TypeChecker_Env.Inlining  -> true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____20541 -> false))
                         in
                      let uu___176_20542 = cfg  in
                      {
                        steps =
                          (let uu___177_20545 = cfg.steps  in
                           {
                             beta = (uu___177_20545.beta);
                             iota = (uu___177_20545.iota);
                             zeta = false;
                             weak = (uu___177_20545.weak);
                             hnf = (uu___177_20545.hnf);
                             primops = (uu___177_20545.primops);
                             no_delta_steps = (uu___177_20545.no_delta_steps);
                             unfold_until = (uu___177_20545.unfold_until);
                             unfold_only = (uu___177_20545.unfold_only);
                             unfold_fully = (uu___177_20545.unfold_fully);
                             unfold_attr = (uu___177_20545.unfold_attr);
                             unfold_tac = (uu___177_20545.unfold_tac);
                             pure_subterms_within_computations =
                               (uu___177_20545.pure_subterms_within_computations);
                             simplify = (uu___177_20545.simplify);
                             erase_universes =
                               (uu___177_20545.erase_universes);
                             allow_unbound_universes =
                               (uu___177_20545.allow_unbound_universes);
                             reify_ = (uu___177_20545.reify_);
                             compress_uvars = (uu___177_20545.compress_uvars);
                             no_full_norm = (uu___177_20545.no_full_norm);
                             check_no_uvars = (uu___177_20545.check_no_uvars);
                             unmeta = (uu___177_20545.unmeta);
                             unascribe = (uu___177_20545.unascribe)
                           });
                        tcenv = (uu___176_20542.tcenv);
                        debug = (uu___176_20542.debug);
                        delta_level = new_delta;
                        primitive_steps = (uu___176_20542.primitive_steps);
                        strong = true;
                        memoize_lazy = (uu___176_20542.memoize_lazy);
                        normalize_pure_lets =
                          (uu___176_20542.normalize_pure_lets)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_iota_zeta env2 t2
                      else norm cfg_exclude_iota_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____20577 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____20598 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____20658  ->
                                    fun uu____20659  ->
                                      match (uu____20658, uu____20659) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____20750 = norm_pat env3 p1
                                             in
                                          (match uu____20750 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____20598 with
                           | (pats1,env3) ->
                               ((let uu___178_20832 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___178_20832.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___179_20851 = x  in
                            let uu____20852 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___179_20851.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___179_20851.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20852
                            }  in
                          ((let uu___180_20866 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___180_20866.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___181_20877 = x  in
                            let uu____20878 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___181_20877.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___181_20877.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20878
                            }  in
                          ((let uu___182_20892 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___182_20892.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___183_20908 = x  in
                            let uu____20909 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___183_20908.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___183_20908.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20909
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___184_20916 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___184_20916.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____20926 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____20940 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____20940 with
                                  | (p,wopt,e) ->
                                      let uu____20960 = norm_pat env1 p  in
                                      (match uu____20960 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____20985 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____20985
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let uu____20991 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee, branches1))
                        r
                       in
                    rebuild cfg env1 stack1 uu____20991)
                    in
                 let rec is_cons head1 =
                   let uu____20996 =
                     let uu____20997 = FStar_Syntax_Subst.compress head1  in
                     uu____20997.FStar_Syntax_Syntax.n  in
                   match uu____20996 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____21001) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____21006 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21007;
                         FStar_Syntax_Syntax.fv_delta = uu____21008;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____21009;
                         FStar_Syntax_Syntax.fv_delta = uu____21010;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____21011);_}
                       -> true
                   | uu____21018 -> false  in
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
                   let uu____21163 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____21163 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____21250 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____21289 ->
                                 let uu____21290 =
                                   let uu____21291 = is_cons head1  in
                                   Prims.op_Negation uu____21291  in
                                 FStar_Util.Inr uu____21290)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____21316 =
                              let uu____21317 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____21317.FStar_Syntax_Syntax.n  in
                            (match uu____21316 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____21335 ->
                                 let uu____21336 =
                                   let uu____21337 = is_cons head1  in
                                   Prims.op_Negation uu____21337  in
                                 FStar_Util.Inr uu____21336))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____21406)::rest_a,(p1,uu____21409)::rest_p) ->
                       let uu____21453 = matches_pat t2 p1  in
                       (match uu____21453 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____21502 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____21608 = matches_pat scrutinee1 p1  in
                       (match uu____21608 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (log cfg
                               (fun uu____21648  ->
                                  let uu____21649 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____21650 =
                                    let uu____21651 =
                                      FStar_List.map
                                        (fun uu____21661  ->
                                           match uu____21661 with
                                           | (uu____21666,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____21651
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____21649 uu____21650);
                             (let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____21697  ->
                                       match uu____21697 with
                                       | (bv,t2) ->
                                           let uu____21720 =
                                             let uu____21727 =
                                               let uu____21730 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____21730
                                                in
                                             let uu____21731 =
                                               let uu____21732 =
                                                 let uu____21763 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____21763, false)
                                                  in
                                               Clos uu____21732  in
                                             (uu____21727, uu____21731)  in
                                           uu____21720 :: env2) env1 s
                                 in
                              let uu____21880 = guard_when_clause wopt b rest
                                 in
                              norm cfg env2 stack1 uu____21880)))
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
    let uu____21903 =
      let uu____21906 = FStar_ST.op_Bang plugins  in p :: uu____21906  in
    FStar_ST.op_Colon_Equals plugins uu____21903  in
  let retrieve uu____22004 = FStar_ST.op_Bang plugins  in
  (register, retrieve) 
let (register_plugin : primitive_step -> Prims.unit) =
  fun p  -> FStar_Pervasives_Native.fst plugins p 
let (retrieve_plugins : Prims.unit -> primitive_step Prims.list) =
  fun uu____22069  -> FStar_Pervasives_Native.snd plugins () 
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
               (fun uu___92_22102  ->
                  match uu___92_22102 with
                  | UnfoldUntil k -> [FStar_TypeChecker_Env.Unfold k]
                  | Eager_unfolding  ->
                      [FStar_TypeChecker_Env.Eager_unfolding_only]
                  | Inlining  -> [FStar_TypeChecker_Env.Inlining]
                  | UnfoldTac  -> [FStar_TypeChecker_Env.UnfoldTac]
                  | uu____22106 -> []))
           in
        let d1 =
          match d with
          | [] -> [FStar_TypeChecker_Env.NoDelta]
          | uu____22112 -> d  in
        let uu____22115 = to_fsteps s  in
        let uu____22116 =
          let uu____22117 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Norm")  in
          let uu____22118 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "Primops")  in
          let uu____22119 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "380")  in
          let uu____22120 =
            FStar_TypeChecker_Env.debug e (FStar_Options.Other "NormDelayed")
             in
          let uu____22121 =
            FStar_TypeChecker_Env.debug e
              (FStar_Options.Other "print_normalized_terms")
             in
          {
            gen = uu____22117;
            primop = uu____22118;
            b380 = uu____22119;
            norm_delayed = uu____22120;
            print_normalized = uu____22121
          }  in
        let uu____22122 =
          let uu____22125 =
            let uu____22128 = retrieve_plugins ()  in
            FStar_List.append uu____22128 psteps  in
          add_steps built_in_primitive_steps uu____22125  in
        let uu____22131 =
          (FStar_Options.normalize_pure_terms_for_extraction ()) ||
            (let uu____22133 =
               FStar_All.pipe_right s
                 (FStar_List.contains PureSubtermsWithinComputations)
                in
             Prims.op_Negation uu____22133)
           in
        {
          steps = uu____22115;
          tcenv = e;
          debug = uu____22116;
          delta_level = d1;
          primitive_steps = uu____22122;
          strong = false;
          memoize_lazy = true;
          normalize_pure_lets = uu____22131
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
      fun t  -> let uu____22191 = config s e  in norm_comp uu____22191 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____22204 = config [] env  in norm_universe uu____22204 [] u
  
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
        let uu____22222 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____22222  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____22229 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___185_22248 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___185_22248.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___185_22248.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____22255 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____22255
          then
            let ct1 =
              let uu____22257 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____22257 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____22264 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____22264
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___186_22268 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___186_22268.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___186_22268.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___186_22268.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c
                     in
                  let uu___187_22270 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___187_22270.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___187_22270.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___187_22270.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___187_22270.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___188_22271 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___188_22271.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___188_22271.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____22273 -> c
  
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
        let uu____22285 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____22285  in
      let uu____22292 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____22292
      then
        let uu____22293 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____22293 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____22299  ->
                 let uu____22300 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____22300)
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
            ((let uu____22317 =
                let uu____22322 =
                  let uu____22323 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22323
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22322)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____22317);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____22334 = config [AllowUnboundUniverses] env  in
          norm_comp uu____22334 [] c
        with
        | e ->
            ((let uu____22347 =
                let uu____22352 =
                  let uu____22353 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____22353
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____22352)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____22347);
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
                   let uu____22390 =
                     let uu____22391 =
                       let uu____22398 = FStar_Syntax_Util.mk_conj phi1 phi
                          in
                       (y, uu____22398)  in
                     FStar_Syntax_Syntax.Tm_refine uu____22391  in
                   mk uu____22390 t01.FStar_Syntax_Syntax.pos
               | uu____22403 -> t2)
          | uu____22404 -> t2  in
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
        let uu____22444 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____22444 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____22473 ->
                 let uu____22480 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____22480 with
                  | (actuals,uu____22490,uu____22491) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____22505 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____22505 with
                         | (binders,args) ->
                             let uu____22522 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____22522
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
      | uu____22530 ->
          let uu____22531 = FStar_Syntax_Util.head_and_args t  in
          (match uu____22531 with
           | (head1,args) ->
               let uu____22568 =
                 let uu____22569 = FStar_Syntax_Subst.compress head1  in
                 uu____22569.FStar_Syntax_Syntax.n  in
               (match uu____22568 with
                | FStar_Syntax_Syntax.Tm_uvar (uu____22572,thead) ->
                    let uu____22598 = FStar_Syntax_Util.arrow_formals thead
                       in
                    (match uu____22598 with
                     | (formals,tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____22640 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___193_22648 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___193_22648.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___193_22648.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___193_22648.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___193_22648.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___193_22648.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___193_22648.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___193_22648.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___193_22648.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___193_22648.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___193_22648.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___193_22648.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___193_22648.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___193_22648.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___193_22648.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___193_22648.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___193_22648.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___193_22648.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___193_22648.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___193_22648.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___193_22648.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___193_22648.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___193_22648.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___193_22648.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___193_22648.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___193_22648.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___193_22648.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___193_22648.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___193_22648.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___193_22648.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___193_22648.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___193_22648.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___193_22648.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___193_22648.FStar_TypeChecker_Env.dep_graph)
                                 }) t
                               in
                            match uu____22640 with
                            | (uu____22649,ty,uu____22651) ->
                                eta_expand_with_type env t ty))
                | uu____22652 ->
                    let uu____22653 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___194_22661 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___194_22661.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___194_22661.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___194_22661.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___194_22661.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___194_22661.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___194_22661.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___194_22661.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___194_22661.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___194_22661.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___194_22661.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___194_22661.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___194_22661.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___194_22661.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___194_22661.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___194_22661.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___194_22661.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___194_22661.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___194_22661.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___194_22661.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___194_22661.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___194_22661.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___194_22661.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___194_22661.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___194_22661.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___194_22661.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___194_22661.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___194_22661.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___194_22661.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___194_22661.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___194_22661.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___194_22661.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___194_22661.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___194_22661.FStar_TypeChecker_Env.dep_graph)
                         }) t
                       in
                    (match uu____22653 with
                     | (uu____22662,ty,uu____22664) ->
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
      let uu___195_22721 = x  in
      let uu____22722 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___195_22721.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___195_22721.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____22722
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____22725 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____22750 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____22751 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____22752 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____22753 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____22760 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____22761 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____22762 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___196_22790 = rc  in
          let uu____22791 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____22798 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___196_22790.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____22791;
            FStar_Syntax_Syntax.residual_flags = uu____22798
          }  in
        let uu____22801 =
          let uu____22802 =
            let uu____22819 = elim_delayed_subst_binders bs  in
            let uu____22826 = elim_delayed_subst_term t2  in
            let uu____22827 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____22819, uu____22826, uu____22827)  in
          FStar_Syntax_Syntax.Tm_abs uu____22802  in
        mk1 uu____22801
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____22856 =
          let uu____22857 =
            let uu____22870 = elim_delayed_subst_binders bs  in
            let uu____22877 = elim_delayed_subst_comp c  in
            (uu____22870, uu____22877)  in
          FStar_Syntax_Syntax.Tm_arrow uu____22857  in
        mk1 uu____22856
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____22890 =
          let uu____22891 =
            let uu____22898 = elim_bv bv  in
            let uu____22899 = elim_delayed_subst_term phi  in
            (uu____22898, uu____22899)  in
          FStar_Syntax_Syntax.Tm_refine uu____22891  in
        mk1 uu____22890
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____22922 =
          let uu____22923 =
            let uu____22938 = elim_delayed_subst_term t2  in
            let uu____22939 = elim_delayed_subst_args args  in
            (uu____22938, uu____22939)  in
          FStar_Syntax_Syntax.Tm_app uu____22923  in
        mk1 uu____22922
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___197_23003 = p  in
              let uu____23004 =
                let uu____23005 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____23005  in
              {
                FStar_Syntax_Syntax.v = uu____23004;
                FStar_Syntax_Syntax.p =
                  (uu___197_23003.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___198_23007 = p  in
              let uu____23008 =
                let uu____23009 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____23009  in
              {
                FStar_Syntax_Syntax.v = uu____23008;
                FStar_Syntax_Syntax.p =
                  (uu___198_23007.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___199_23016 = p  in
              let uu____23017 =
                let uu____23018 =
                  let uu____23025 = elim_bv x  in
                  let uu____23026 = elim_delayed_subst_term t0  in
                  (uu____23025, uu____23026)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____23018  in
              {
                FStar_Syntax_Syntax.v = uu____23017;
                FStar_Syntax_Syntax.p =
                  (uu___199_23016.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___200_23045 = p  in
              let uu____23046 =
                let uu____23047 =
                  let uu____23060 =
                    FStar_List.map
                      (fun uu____23083  ->
                         match uu____23083 with
                         | (x,b) ->
                             let uu____23096 = elim_pat x  in
                             (uu____23096, b)) pats
                     in
                  (fv, uu____23060)  in
                FStar_Syntax_Syntax.Pat_cons uu____23047  in
              {
                FStar_Syntax_Syntax.v = uu____23046;
                FStar_Syntax_Syntax.p =
                  (uu___200_23045.FStar_Syntax_Syntax.p)
              }
          | uu____23109 -> p  in
        let elim_branch uu____23131 =
          match uu____23131 with
          | (pat,wopt,t3) ->
              let uu____23157 = elim_pat pat  in
              let uu____23160 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____23163 = elim_delayed_subst_term t3  in
              (uu____23157, uu____23160, uu____23163)
           in
        let uu____23168 =
          let uu____23169 =
            let uu____23192 = elim_delayed_subst_term t2  in
            let uu____23193 = FStar_List.map elim_branch branches  in
            (uu____23192, uu____23193)  in
          FStar_Syntax_Syntax.Tm_match uu____23169  in
        mk1 uu____23168
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____23302 =
          match uu____23302 with
          | (tc,topt) ->
              let uu____23337 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____23347 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____23347
                | FStar_Util.Inr c ->
                    let uu____23349 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____23349
                 in
              let uu____23350 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____23337, uu____23350)
           in
        let uu____23359 =
          let uu____23360 =
            let uu____23387 = elim_delayed_subst_term t2  in
            let uu____23388 = elim_ascription a  in
            (uu____23387, uu____23388, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____23360  in
        mk1 uu____23359
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___201_23433 = lb  in
          let uu____23434 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____23437 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___201_23433.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___201_23433.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____23434;
            FStar_Syntax_Syntax.lbeff =
              (uu___201_23433.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____23437;
            FStar_Syntax_Syntax.lbattrs =
              (uu___201_23433.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___201_23433.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____23440 =
          let uu____23441 =
            let uu____23454 =
              let uu____23461 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____23461)  in
            let uu____23470 = elim_delayed_subst_term t2  in
            (uu____23454, uu____23470)  in
          FStar_Syntax_Syntax.Tm_let uu____23441  in
        mk1 uu____23440
    | FStar_Syntax_Syntax.Tm_uvar (uv,t2) ->
        let uu____23503 =
          let uu____23504 =
            let uu____23521 = elim_delayed_subst_term t2  in
            (uv, uu____23521)  in
          FStar_Syntax_Syntax.Tm_uvar uu____23504  in
        mk1 uu____23503
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____23539 =
          let uu____23540 =
            let uu____23547 = elim_delayed_subst_term tm  in
            (uu____23547, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____23540  in
        mk1 uu____23539
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____23554 =
          let uu____23555 =
            let uu____23562 = elim_delayed_subst_term t2  in
            let uu____23563 = elim_delayed_subst_meta md  in
            (uu____23562, uu____23563)  in
          FStar_Syntax_Syntax.Tm_meta uu____23555  in
        mk1 uu____23554

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___93_23570  ->
         match uu___93_23570 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____23574 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____23574
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
        let uu____23595 =
          let uu____23596 =
            let uu____23605 = elim_delayed_subst_term t  in
            (uu____23605, uopt)  in
          FStar_Syntax_Syntax.Total uu____23596  in
        mk1 uu____23595
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____23618 =
          let uu____23619 =
            let uu____23628 = elim_delayed_subst_term t  in
            (uu____23628, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____23619  in
        mk1 uu____23618
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___202_23633 = ct  in
          let uu____23634 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____23637 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____23646 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___202_23633.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___202_23633.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____23634;
            FStar_Syntax_Syntax.effect_args = uu____23637;
            FStar_Syntax_Syntax.flags = uu____23646
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___94_23649  ->
    match uu___94_23649 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____23661 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____23661
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____23694 =
          let uu____23701 = elim_delayed_subst_term t  in (m, uu____23701)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____23694
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____23709 =
          let uu____23718 = elim_delayed_subst_term t  in
          (m1, m2, uu____23718)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____23709
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____23741  ->
         match uu____23741 with
         | (t,q) ->
             let uu____23752 = elim_delayed_subst_term t  in (uu____23752, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____23772  ->
         match uu____23772 with
         | (x,q) ->
             let uu____23783 =
               let uu___203_23784 = x  in
               let uu____23785 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___203_23784.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___203_23784.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____23785
               }  in
             (uu____23783, q)) bs

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
            | (uu____23861,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____23867,FStar_Util.Inl t) ->
                let uu____23873 =
                  let uu____23876 =
                    let uu____23877 =
                      let uu____23890 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____23890)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____23877  in
                  FStar_Syntax_Syntax.mk uu____23876  in
                uu____23873 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____23894 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____23894 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____23922 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____23977 ->
                    let uu____23978 =
                      let uu____23987 =
                        let uu____23988 = FStar_Syntax_Subst.compress t4  in
                        uu____23988.FStar_Syntax_Syntax.n  in
                      (uu____23987, tc)  in
                    (match uu____23978 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____24013) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____24050) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____24089,FStar_Util.Inl uu____24090) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____24113 -> failwith "Impossible")
                 in
              (match uu____23922 with
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
          let uu____24218 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____24218 with
          | (univ_names1,binders1,tc) ->
              let uu____24276 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____24276)
  
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
          let uu____24311 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____24311 with
          | (univ_names1,binders1,tc) ->
              let uu____24371 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____24371)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____24404 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____24404 with
           | (univ_names1,binders1,typ1) ->
               let uu___204_24432 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___204_24432.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___204_24432.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___204_24432.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___204_24432.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___205_24453 = s  in
          let uu____24454 =
            let uu____24455 =
              let uu____24464 = FStar_List.map (elim_uvars env) sigs  in
              (uu____24464, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____24455  in
          {
            FStar_Syntax_Syntax.sigel = uu____24454;
            FStar_Syntax_Syntax.sigrng =
              (uu___205_24453.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___205_24453.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___205_24453.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___205_24453.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____24481 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24481 with
           | (univ_names1,uu____24499,typ1) ->
               let uu___206_24513 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___206_24513.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___206_24513.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___206_24513.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___206_24513.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____24519 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24519 with
           | (univ_names1,uu____24537,typ1) ->
               let uu___207_24551 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___207_24551.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___207_24551.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___207_24551.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___207_24551.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____24585 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____24585 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____24608 =
                            let uu____24609 =
                              let uu____24610 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____24610  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____24609
                             in
                          elim_delayed_subst_term uu____24608  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___208_24613 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___208_24613.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___208_24613.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___208_24613.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___208_24613.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___209_24614 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___209_24614.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___209_24614.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___209_24614.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___209_24614.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___210_24626 = s  in
          let uu____24627 =
            let uu____24628 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____24628  in
          {
            FStar_Syntax_Syntax.sigel = uu____24627;
            FStar_Syntax_Syntax.sigrng =
              (uu___210_24626.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___210_24626.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___210_24626.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___210_24626.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____24632 = elim_uvars_aux_t env us [] t  in
          (match uu____24632 with
           | (us1,uu____24650,t1) ->
               let uu___211_24664 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___211_24664.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___211_24664.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___211_24664.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___211_24664.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24665 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____24667 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____24667 with
           | (univs1,binders,signature) ->
               let uu____24695 =
                 let uu____24704 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____24704 with
                 | (univs_opening,univs2) ->
                     let uu____24731 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____24731)
                  in
               (match uu____24695 with
                | (univs_opening,univs_closing) ->
                    let uu____24748 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____24754 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____24755 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____24754, uu____24755)  in
                    (match uu____24748 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____24777 =
                           match uu____24777 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____24795 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____24795 with
                                | (us1,t1) ->
                                    let uu____24806 =
                                      let uu____24811 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____24818 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____24811, uu____24818)  in
                                    (match uu____24806 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____24831 =
                                           let uu____24836 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____24845 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____24836, uu____24845)  in
                                         (match uu____24831 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____24861 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____24861
                                                 in
                                              let uu____24862 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____24862 with
                                               | (uu____24883,uu____24884,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____24899 =
                                                       let uu____24900 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____24900
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____24899
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____24905 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____24905 with
                           | (uu____24918,uu____24919,t1) -> t1  in
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
                             | uu____24979 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____24996 =
                               let uu____24997 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____24997.FStar_Syntax_Syntax.n  in
                             match uu____24996 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____25056 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____25085 =
                               let uu____25086 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____25086.FStar_Syntax_Syntax.n  in
                             match uu____25085 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____25107) ->
                                 let uu____25128 = destruct_action_body body
                                    in
                                 (match uu____25128 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____25173 ->
                                 let uu____25174 = destruct_action_body t  in
                                 (match uu____25174 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____25223 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____25223 with
                           | (action_univs,t) ->
                               let uu____25232 = destruct_action_typ_templ t
                                  in
                               (match uu____25232 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___212_25273 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___212_25273.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___212_25273.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___213_25275 = ed  in
                           let uu____25276 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____25277 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____25278 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____25279 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____25280 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____25281 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____25282 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____25283 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____25284 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____25285 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____25286 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____25287 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____25288 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____25289 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___213_25275.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___213_25275.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____25276;
                             FStar_Syntax_Syntax.bind_wp = uu____25277;
                             FStar_Syntax_Syntax.if_then_else = uu____25278;
                             FStar_Syntax_Syntax.ite_wp = uu____25279;
                             FStar_Syntax_Syntax.stronger = uu____25280;
                             FStar_Syntax_Syntax.close_wp = uu____25281;
                             FStar_Syntax_Syntax.assert_p = uu____25282;
                             FStar_Syntax_Syntax.assume_p = uu____25283;
                             FStar_Syntax_Syntax.null_wp = uu____25284;
                             FStar_Syntax_Syntax.trivial = uu____25285;
                             FStar_Syntax_Syntax.repr = uu____25286;
                             FStar_Syntax_Syntax.return_repr = uu____25287;
                             FStar_Syntax_Syntax.bind_repr = uu____25288;
                             FStar_Syntax_Syntax.actions = uu____25289;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___213_25275.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___214_25292 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___214_25292.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___214_25292.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___214_25292.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___214_25292.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___95_25309 =
            match uu___95_25309 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____25336 = elim_uvars_aux_t env us [] t  in
                (match uu____25336 with
                 | (us1,uu____25360,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___215_25379 = sub_eff  in
            let uu____25380 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____25383 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___215_25379.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___215_25379.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____25380;
              FStar_Syntax_Syntax.lift = uu____25383
            }  in
          let uu___216_25386 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___216_25386.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___216_25386.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___216_25386.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___216_25386.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____25396 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____25396 with
           | (univ_names1,binders1,comp1) ->
               let uu___217_25430 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___217_25430.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___217_25430.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___217_25430.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___217_25430.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____25441 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____25442 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> normalize [EraseUniverses; AllowUnboundUniverses] env t
  