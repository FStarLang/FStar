
open Prims
open FStar_Pervasives
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
| Unascribe


let uu___is_Beta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Beta -> begin
true
end
| uu____35 -> begin
false
end))


let uu___is_Iota : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iota -> begin
true
end
| uu____41 -> begin
false
end))


let uu___is_Zeta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Zeta -> begin
true
end
| uu____47 -> begin
false
end))


let uu___is_Exclude : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exclude (_0) -> begin
true
end
| uu____54 -> begin
false
end))


let __proj__Exclude__item___0 : step  ->  step = (fun projectee -> (match (projectee) with
| Exclude (_0) -> begin
_0
end))


let uu___is_Weak : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Weak -> begin
true
end
| uu____67 -> begin
false
end))


let uu___is_HNF : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| HNF -> begin
true
end
| uu____73 -> begin
false
end))


let uu___is_Primops : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primops -> begin
true
end
| uu____79 -> begin
false
end))


let uu___is_Eager_unfolding : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding -> begin
true
end
| uu____85 -> begin
false
end))


let uu___is_Inlining : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inlining -> begin
true
end
| uu____91 -> begin
false
end))


let uu___is_DoNotUnfoldPureLets : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| DoNotUnfoldPureLets -> begin
true
end
| uu____97 -> begin
false
end))


let uu___is_UnfoldUntil : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
true
end
| uu____104 -> begin
false
end))


let __proj__UnfoldUntil__item___0 : step  ->  FStar_Syntax_Syntax.delta_depth = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
_0
end))


let uu___is_UnfoldOnly : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
true
end
| uu____120 -> begin
false
end))


let __proj__UnfoldOnly__item___0 : step  ->  FStar_Ident.lid Prims.list = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
_0
end))


let uu___is_UnfoldFully : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldFully (_0) -> begin
true
end
| uu____142 -> begin
false
end))


let __proj__UnfoldFully__item___0 : step  ->  FStar_Ident.lid Prims.list = (fun projectee -> (match (projectee) with
| UnfoldFully (_0) -> begin
_0
end))


let uu___is_UnfoldAttr : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldAttr (_0) -> begin
true
end
| uu____162 -> begin
false
end))


let __proj__UnfoldAttr__item___0 : step  ->  FStar_Syntax_Syntax.attribute = (fun projectee -> (match (projectee) with
| UnfoldAttr (_0) -> begin
_0
end))


let uu___is_UnfoldTac : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldTac -> begin
true
end
| uu____175 -> begin
false
end))


let uu___is_PureSubtermsWithinComputations : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PureSubtermsWithinComputations -> begin
true
end
| uu____181 -> begin
false
end))


let uu___is_Simplify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Simplify -> begin
true
end
| uu____187 -> begin
false
end))


let uu___is_EraseUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EraseUniverses -> begin
true
end
| uu____193 -> begin
false
end))


let uu___is_AllowUnboundUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AllowUnboundUniverses -> begin
true
end
| uu____199 -> begin
false
end))


let uu___is_Reify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reify -> begin
true
end
| uu____205 -> begin
false
end))


let uu___is_CompressUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CompressUvars -> begin
true
end
| uu____211 -> begin
false
end))


let uu___is_NoFullNorm : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoFullNorm -> begin
true
end
| uu____217 -> begin
false
end))


let uu___is_CheckNoUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CheckNoUvars -> begin
true
end
| uu____223 -> begin
false
end))


let uu___is_Unmeta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unmeta -> begin
true
end
| uu____229 -> begin
false
end))


let uu___is_Unascribe : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unascribe -> begin
true
end
| uu____235 -> begin
false
end))


type steps =
step Prims.list


let cases : 'Auu____248 'Auu____249 . ('Auu____248  ->  'Auu____249)  ->  'Auu____249  ->  'Auu____248 FStar_Pervasives_Native.option  ->  'Auu____249 = (fun f d uu___80_269 -> (match (uu___80_269) with
| FStar_Pervasives_Native.Some (x) -> begin
(f x)
end
| FStar_Pervasives_Native.None -> begin
d
end))

type fsteps =
{beta : Prims.bool; iota : Prims.bool; zeta : Prims.bool; weak : Prims.bool; hnf : Prims.bool; primops : Prims.bool; do_not_unfold_pure_lets : Prims.bool; unfold_until : FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option; unfold_only : FStar_Ident.lid Prims.list FStar_Pervasives_Native.option; unfold_fully : FStar_Ident.lid Prims.list FStar_Pervasives_Native.option; unfold_attr : FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option; unfold_tac : Prims.bool; pure_subterms_within_computations : Prims.bool; simplify : Prims.bool; erase_universes : Prims.bool; allow_unbound_universes : Prims.bool; reify_ : Prims.bool; compress_uvars : Prims.bool; no_full_norm : Prims.bool; check_no_uvars : Prims.bool; unmeta : Prims.bool; unascribe : Prims.bool; in_full_norm_request : Prims.bool; weakly_reduce_scrutinee : Prims.bool}


let __proj__Mkfsteps__item__beta : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__beta
end))


let __proj__Mkfsteps__item__iota : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__iota
end))


let __proj__Mkfsteps__item__zeta : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__zeta
end))


let __proj__Mkfsteps__item__weak : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__weak
end))


let __proj__Mkfsteps__item__hnf : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__hnf
end))


let __proj__Mkfsteps__item__primops : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__primops
end))


let __proj__Mkfsteps__item__do_not_unfold_pure_lets : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__do_not_unfold_pure_lets
end))


let __proj__Mkfsteps__item__unfold_until : fsteps  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__unfold_until
end))


let __proj__Mkfsteps__item__unfold_only : fsteps  ->  FStar_Ident.lid Prims.list FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__unfold_only
end))


let __proj__Mkfsteps__item__unfold_fully : fsteps  ->  FStar_Ident.lid Prims.list FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__unfold_fully
end))


let __proj__Mkfsteps__item__unfold_attr : fsteps  ->  FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__unfold_attr
end))


let __proj__Mkfsteps__item__unfold_tac : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__unfold_tac
end))


let __proj__Mkfsteps__item__pure_subterms_within_computations : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__pure_subterms_within_computations
end))


let __proj__Mkfsteps__item__simplify : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__simplify
end))


let __proj__Mkfsteps__item__erase_universes : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__erase_universes
end))


let __proj__Mkfsteps__item__allow_unbound_universes : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__allow_unbound_universes
end))


let __proj__Mkfsteps__item__reify_ : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__reify_
end))


let __proj__Mkfsteps__item__compress_uvars : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__compress_uvars
end))


let __proj__Mkfsteps__item__no_full_norm : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__no_full_norm
end))


let __proj__Mkfsteps__item__check_no_uvars : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__check_no_uvars
end))


let __proj__Mkfsteps__item__unmeta : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__unmeta
end))


let __proj__Mkfsteps__item__unascribe : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__unascribe
end))


let __proj__Mkfsteps__item__in_full_norm_request : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__in_full_norm_request
end))


let __proj__Mkfsteps__item__weakly_reduce_scrutinee : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = __fname__beta; iota = __fname__iota; zeta = __fname__zeta; weak = __fname__weak; hnf = __fname__hnf; primops = __fname__primops; do_not_unfold_pure_lets = __fname__do_not_unfold_pure_lets; unfold_until = __fname__unfold_until; unfold_only = __fname__unfold_only; unfold_fully = __fname__unfold_fully; unfold_attr = __fname__unfold_attr; unfold_tac = __fname__unfold_tac; pure_subterms_within_computations = __fname__pure_subterms_within_computations; simplify = __fname__simplify; erase_universes = __fname__erase_universes; allow_unbound_universes = __fname__allow_unbound_universes; reify_ = __fname__reify_; compress_uvars = __fname__compress_uvars; no_full_norm = __fname__no_full_norm; check_no_uvars = __fname__check_no_uvars; unmeta = __fname__unmeta; unascribe = __fname__unascribe; in_full_norm_request = __fname__in_full_norm_request; weakly_reduce_scrutinee = __fname__weakly_reduce_scrutinee} -> begin
__fname__weakly_reduce_scrutinee
end))


let default_steps : fsteps = {beta = true; iota = true; zeta = true; weak = false; hnf = false; primops = false; do_not_unfold_pure_lets = false; unfold_until = FStar_Pervasives_Native.None; unfold_only = FStar_Pervasives_Native.None; unfold_fully = FStar_Pervasives_Native.None; unfold_attr = FStar_Pervasives_Native.None; unfold_tac = false; pure_subterms_within_computations = false; simplify = false; erase_universes = false; allow_unbound_universes = false; reify_ = false; compress_uvars = false; no_full_norm = false; check_no_uvars = false; unmeta = false; unascribe = false; in_full_norm_request = false; weakly_reduce_scrutinee = true}


let fstep_add_one : step  ->  fsteps  ->  fsteps = (fun s fs -> (

let add_opt = (fun x uu___81_1503 -> (match (uu___81_1503) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some ((x)::[])
end
| FStar_Pervasives_Native.Some (xs) -> begin
FStar_Pervasives_Native.Some ((x)::xs)
end))
in (match (s) with
| Beta -> begin
(

let uu___99_1523 = fs
in {beta = true; iota = uu___99_1523.iota; zeta = uu___99_1523.zeta; weak = uu___99_1523.weak; hnf = uu___99_1523.hnf; primops = uu___99_1523.primops; do_not_unfold_pure_lets = uu___99_1523.do_not_unfold_pure_lets; unfold_until = uu___99_1523.unfold_until; unfold_only = uu___99_1523.unfold_only; unfold_fully = uu___99_1523.unfold_fully; unfold_attr = uu___99_1523.unfold_attr; unfold_tac = uu___99_1523.unfold_tac; pure_subterms_within_computations = uu___99_1523.pure_subterms_within_computations; simplify = uu___99_1523.simplify; erase_universes = uu___99_1523.erase_universes; allow_unbound_universes = uu___99_1523.allow_unbound_universes; reify_ = uu___99_1523.reify_; compress_uvars = uu___99_1523.compress_uvars; no_full_norm = uu___99_1523.no_full_norm; check_no_uvars = uu___99_1523.check_no_uvars; unmeta = uu___99_1523.unmeta; unascribe = uu___99_1523.unascribe; in_full_norm_request = uu___99_1523.in_full_norm_request; weakly_reduce_scrutinee = uu___99_1523.weakly_reduce_scrutinee})
end
| Iota -> begin
(

let uu___100_1524 = fs
in {beta = uu___100_1524.beta; iota = true; zeta = uu___100_1524.zeta; weak = uu___100_1524.weak; hnf = uu___100_1524.hnf; primops = uu___100_1524.primops; do_not_unfold_pure_lets = uu___100_1524.do_not_unfold_pure_lets; unfold_until = uu___100_1524.unfold_until; unfold_only = uu___100_1524.unfold_only; unfold_fully = uu___100_1524.unfold_fully; unfold_attr = uu___100_1524.unfold_attr; unfold_tac = uu___100_1524.unfold_tac; pure_subterms_within_computations = uu___100_1524.pure_subterms_within_computations; simplify = uu___100_1524.simplify; erase_universes = uu___100_1524.erase_universes; allow_unbound_universes = uu___100_1524.allow_unbound_universes; reify_ = uu___100_1524.reify_; compress_uvars = uu___100_1524.compress_uvars; no_full_norm = uu___100_1524.no_full_norm; check_no_uvars = uu___100_1524.check_no_uvars; unmeta = uu___100_1524.unmeta; unascribe = uu___100_1524.unascribe; in_full_norm_request = uu___100_1524.in_full_norm_request; weakly_reduce_scrutinee = uu___100_1524.weakly_reduce_scrutinee})
end
| Zeta -> begin
(

let uu___101_1525 = fs
in {beta = uu___101_1525.beta; iota = uu___101_1525.iota; zeta = true; weak = uu___101_1525.weak; hnf = uu___101_1525.hnf; primops = uu___101_1525.primops; do_not_unfold_pure_lets = uu___101_1525.do_not_unfold_pure_lets; unfold_until = uu___101_1525.unfold_until; unfold_only = uu___101_1525.unfold_only; unfold_fully = uu___101_1525.unfold_fully; unfold_attr = uu___101_1525.unfold_attr; unfold_tac = uu___101_1525.unfold_tac; pure_subterms_within_computations = uu___101_1525.pure_subterms_within_computations; simplify = uu___101_1525.simplify; erase_universes = uu___101_1525.erase_universes; allow_unbound_universes = uu___101_1525.allow_unbound_universes; reify_ = uu___101_1525.reify_; compress_uvars = uu___101_1525.compress_uvars; no_full_norm = uu___101_1525.no_full_norm; check_no_uvars = uu___101_1525.check_no_uvars; unmeta = uu___101_1525.unmeta; unascribe = uu___101_1525.unascribe; in_full_norm_request = uu___101_1525.in_full_norm_request; weakly_reduce_scrutinee = uu___101_1525.weakly_reduce_scrutinee})
end
| Exclude (Beta) -> begin
(

let uu___102_1526 = fs
in {beta = false; iota = uu___102_1526.iota; zeta = uu___102_1526.zeta; weak = uu___102_1526.weak; hnf = uu___102_1526.hnf; primops = uu___102_1526.primops; do_not_unfold_pure_lets = uu___102_1526.do_not_unfold_pure_lets; unfold_until = uu___102_1526.unfold_until; unfold_only = uu___102_1526.unfold_only; unfold_fully = uu___102_1526.unfold_fully; unfold_attr = uu___102_1526.unfold_attr; unfold_tac = uu___102_1526.unfold_tac; pure_subterms_within_computations = uu___102_1526.pure_subterms_within_computations; simplify = uu___102_1526.simplify; erase_universes = uu___102_1526.erase_universes; allow_unbound_universes = uu___102_1526.allow_unbound_universes; reify_ = uu___102_1526.reify_; compress_uvars = uu___102_1526.compress_uvars; no_full_norm = uu___102_1526.no_full_norm; check_no_uvars = uu___102_1526.check_no_uvars; unmeta = uu___102_1526.unmeta; unascribe = uu___102_1526.unascribe; in_full_norm_request = uu___102_1526.in_full_norm_request; weakly_reduce_scrutinee = uu___102_1526.weakly_reduce_scrutinee})
end
| Exclude (Iota) -> begin
(

let uu___103_1527 = fs
in {beta = uu___103_1527.beta; iota = false; zeta = uu___103_1527.zeta; weak = uu___103_1527.weak; hnf = uu___103_1527.hnf; primops = uu___103_1527.primops; do_not_unfold_pure_lets = uu___103_1527.do_not_unfold_pure_lets; unfold_until = uu___103_1527.unfold_until; unfold_only = uu___103_1527.unfold_only; unfold_fully = uu___103_1527.unfold_fully; unfold_attr = uu___103_1527.unfold_attr; unfold_tac = uu___103_1527.unfold_tac; pure_subterms_within_computations = uu___103_1527.pure_subterms_within_computations; simplify = uu___103_1527.simplify; erase_universes = uu___103_1527.erase_universes; allow_unbound_universes = uu___103_1527.allow_unbound_universes; reify_ = uu___103_1527.reify_; compress_uvars = uu___103_1527.compress_uvars; no_full_norm = uu___103_1527.no_full_norm; check_no_uvars = uu___103_1527.check_no_uvars; unmeta = uu___103_1527.unmeta; unascribe = uu___103_1527.unascribe; in_full_norm_request = uu___103_1527.in_full_norm_request; weakly_reduce_scrutinee = uu___103_1527.weakly_reduce_scrutinee})
end
| Exclude (Zeta) -> begin
(

let uu___104_1528 = fs
in {beta = uu___104_1528.beta; iota = uu___104_1528.iota; zeta = false; weak = uu___104_1528.weak; hnf = uu___104_1528.hnf; primops = uu___104_1528.primops; do_not_unfold_pure_lets = uu___104_1528.do_not_unfold_pure_lets; unfold_until = uu___104_1528.unfold_until; unfold_only = uu___104_1528.unfold_only; unfold_fully = uu___104_1528.unfold_fully; unfold_attr = uu___104_1528.unfold_attr; unfold_tac = uu___104_1528.unfold_tac; pure_subterms_within_computations = uu___104_1528.pure_subterms_within_computations; simplify = uu___104_1528.simplify; erase_universes = uu___104_1528.erase_universes; allow_unbound_universes = uu___104_1528.allow_unbound_universes; reify_ = uu___104_1528.reify_; compress_uvars = uu___104_1528.compress_uvars; no_full_norm = uu___104_1528.no_full_norm; check_no_uvars = uu___104_1528.check_no_uvars; unmeta = uu___104_1528.unmeta; unascribe = uu___104_1528.unascribe; in_full_norm_request = uu___104_1528.in_full_norm_request; weakly_reduce_scrutinee = uu___104_1528.weakly_reduce_scrutinee})
end
| Exclude (uu____1529) -> begin
(failwith "Bad exclude")
end
| Weak -> begin
(

let uu___105_1530 = fs
in {beta = uu___105_1530.beta; iota = uu___105_1530.iota; zeta = uu___105_1530.zeta; weak = true; hnf = uu___105_1530.hnf; primops = uu___105_1530.primops; do_not_unfold_pure_lets = uu___105_1530.do_not_unfold_pure_lets; unfold_until = uu___105_1530.unfold_until; unfold_only = uu___105_1530.unfold_only; unfold_fully = uu___105_1530.unfold_fully; unfold_attr = uu___105_1530.unfold_attr; unfold_tac = uu___105_1530.unfold_tac; pure_subterms_within_computations = uu___105_1530.pure_subterms_within_computations; simplify = uu___105_1530.simplify; erase_universes = uu___105_1530.erase_universes; allow_unbound_universes = uu___105_1530.allow_unbound_universes; reify_ = uu___105_1530.reify_; compress_uvars = uu___105_1530.compress_uvars; no_full_norm = uu___105_1530.no_full_norm; check_no_uvars = uu___105_1530.check_no_uvars; unmeta = uu___105_1530.unmeta; unascribe = uu___105_1530.unascribe; in_full_norm_request = uu___105_1530.in_full_norm_request; weakly_reduce_scrutinee = uu___105_1530.weakly_reduce_scrutinee})
end
| HNF -> begin
(

let uu___106_1531 = fs
in {beta = uu___106_1531.beta; iota = uu___106_1531.iota; zeta = uu___106_1531.zeta; weak = uu___106_1531.weak; hnf = true; primops = uu___106_1531.primops; do_not_unfold_pure_lets = uu___106_1531.do_not_unfold_pure_lets; unfold_until = uu___106_1531.unfold_until; unfold_only = uu___106_1531.unfold_only; unfold_fully = uu___106_1531.unfold_fully; unfold_attr = uu___106_1531.unfold_attr; unfold_tac = uu___106_1531.unfold_tac; pure_subterms_within_computations = uu___106_1531.pure_subterms_within_computations; simplify = uu___106_1531.simplify; erase_universes = uu___106_1531.erase_universes; allow_unbound_universes = uu___106_1531.allow_unbound_universes; reify_ = uu___106_1531.reify_; compress_uvars = uu___106_1531.compress_uvars; no_full_norm = uu___106_1531.no_full_norm; check_no_uvars = uu___106_1531.check_no_uvars; unmeta = uu___106_1531.unmeta; unascribe = uu___106_1531.unascribe; in_full_norm_request = uu___106_1531.in_full_norm_request; weakly_reduce_scrutinee = uu___106_1531.weakly_reduce_scrutinee})
end
| Primops -> begin
(

let uu___107_1532 = fs
in {beta = uu___107_1532.beta; iota = uu___107_1532.iota; zeta = uu___107_1532.zeta; weak = uu___107_1532.weak; hnf = uu___107_1532.hnf; primops = true; do_not_unfold_pure_lets = uu___107_1532.do_not_unfold_pure_lets; unfold_until = uu___107_1532.unfold_until; unfold_only = uu___107_1532.unfold_only; unfold_fully = uu___107_1532.unfold_fully; unfold_attr = uu___107_1532.unfold_attr; unfold_tac = uu___107_1532.unfold_tac; pure_subterms_within_computations = uu___107_1532.pure_subterms_within_computations; simplify = uu___107_1532.simplify; erase_universes = uu___107_1532.erase_universes; allow_unbound_universes = uu___107_1532.allow_unbound_universes; reify_ = uu___107_1532.reify_; compress_uvars = uu___107_1532.compress_uvars; no_full_norm = uu___107_1532.no_full_norm; check_no_uvars = uu___107_1532.check_no_uvars; unmeta = uu___107_1532.unmeta; unascribe = uu___107_1532.unascribe; in_full_norm_request = uu___107_1532.in_full_norm_request; weakly_reduce_scrutinee = uu___107_1532.weakly_reduce_scrutinee})
end
| Eager_unfolding -> begin
fs
end
| Inlining -> begin
fs
end
| DoNotUnfoldPureLets -> begin
(

let uu___108_1533 = fs
in {beta = uu___108_1533.beta; iota = uu___108_1533.iota; zeta = uu___108_1533.zeta; weak = uu___108_1533.weak; hnf = uu___108_1533.hnf; primops = uu___108_1533.primops; do_not_unfold_pure_lets = true; unfold_until = uu___108_1533.unfold_until; unfold_only = uu___108_1533.unfold_only; unfold_fully = uu___108_1533.unfold_fully; unfold_attr = uu___108_1533.unfold_attr; unfold_tac = uu___108_1533.unfold_tac; pure_subterms_within_computations = uu___108_1533.pure_subterms_within_computations; simplify = uu___108_1533.simplify; erase_universes = uu___108_1533.erase_universes; allow_unbound_universes = uu___108_1533.allow_unbound_universes; reify_ = uu___108_1533.reify_; compress_uvars = uu___108_1533.compress_uvars; no_full_norm = uu___108_1533.no_full_norm; check_no_uvars = uu___108_1533.check_no_uvars; unmeta = uu___108_1533.unmeta; unascribe = uu___108_1533.unascribe; in_full_norm_request = uu___108_1533.in_full_norm_request; weakly_reduce_scrutinee = uu___108_1533.weakly_reduce_scrutinee})
end
| UnfoldUntil (d) -> begin
(

let uu___109_1535 = fs
in {beta = uu___109_1535.beta; iota = uu___109_1535.iota; zeta = uu___109_1535.zeta; weak = uu___109_1535.weak; hnf = uu___109_1535.hnf; primops = uu___109_1535.primops; do_not_unfold_pure_lets = uu___109_1535.do_not_unfold_pure_lets; unfold_until = FStar_Pervasives_Native.Some (d); unfold_only = uu___109_1535.unfold_only; unfold_fully = uu___109_1535.unfold_fully; unfold_attr = uu___109_1535.unfold_attr; unfold_tac = uu___109_1535.unfold_tac; pure_subterms_within_computations = uu___109_1535.pure_subterms_within_computations; simplify = uu___109_1535.simplify; erase_universes = uu___109_1535.erase_universes; allow_unbound_universes = uu___109_1535.allow_unbound_universes; reify_ = uu___109_1535.reify_; compress_uvars = uu___109_1535.compress_uvars; no_full_norm = uu___109_1535.no_full_norm; check_no_uvars = uu___109_1535.check_no_uvars; unmeta = uu___109_1535.unmeta; unascribe = uu___109_1535.unascribe; in_full_norm_request = uu___109_1535.in_full_norm_request; weakly_reduce_scrutinee = uu___109_1535.weakly_reduce_scrutinee})
end
| UnfoldOnly (lids) -> begin
(

let uu___110_1539 = fs
in {beta = uu___110_1539.beta; iota = uu___110_1539.iota; zeta = uu___110_1539.zeta; weak = uu___110_1539.weak; hnf = uu___110_1539.hnf; primops = uu___110_1539.primops; do_not_unfold_pure_lets = uu___110_1539.do_not_unfold_pure_lets; unfold_until = uu___110_1539.unfold_until; unfold_only = FStar_Pervasives_Native.Some (lids); unfold_fully = uu___110_1539.unfold_fully; unfold_attr = uu___110_1539.unfold_attr; unfold_tac = uu___110_1539.unfold_tac; pure_subterms_within_computations = uu___110_1539.pure_subterms_within_computations; simplify = uu___110_1539.simplify; erase_universes = uu___110_1539.erase_universes; allow_unbound_universes = uu___110_1539.allow_unbound_universes; reify_ = uu___110_1539.reify_; compress_uvars = uu___110_1539.compress_uvars; no_full_norm = uu___110_1539.no_full_norm; check_no_uvars = uu___110_1539.check_no_uvars; unmeta = uu___110_1539.unmeta; unascribe = uu___110_1539.unascribe; in_full_norm_request = uu___110_1539.in_full_norm_request; weakly_reduce_scrutinee = uu___110_1539.weakly_reduce_scrutinee})
end
| UnfoldFully (lids) -> begin
(

let uu___111_1545 = fs
in {beta = uu___111_1545.beta; iota = uu___111_1545.iota; zeta = uu___111_1545.zeta; weak = uu___111_1545.weak; hnf = uu___111_1545.hnf; primops = uu___111_1545.primops; do_not_unfold_pure_lets = uu___111_1545.do_not_unfold_pure_lets; unfold_until = uu___111_1545.unfold_until; unfold_only = uu___111_1545.unfold_only; unfold_fully = FStar_Pervasives_Native.Some (lids); unfold_attr = uu___111_1545.unfold_attr; unfold_tac = uu___111_1545.unfold_tac; pure_subterms_within_computations = uu___111_1545.pure_subterms_within_computations; simplify = uu___111_1545.simplify; erase_universes = uu___111_1545.erase_universes; allow_unbound_universes = uu___111_1545.allow_unbound_universes; reify_ = uu___111_1545.reify_; compress_uvars = uu___111_1545.compress_uvars; no_full_norm = uu___111_1545.no_full_norm; check_no_uvars = uu___111_1545.check_no_uvars; unmeta = uu___111_1545.unmeta; unascribe = uu___111_1545.unascribe; in_full_norm_request = uu___111_1545.in_full_norm_request; weakly_reduce_scrutinee = uu___111_1545.weakly_reduce_scrutinee})
end
| UnfoldAttr (attr) -> begin
(

let uu___112_1549 = fs
in {beta = uu___112_1549.beta; iota = uu___112_1549.iota; zeta = uu___112_1549.zeta; weak = uu___112_1549.weak; hnf = uu___112_1549.hnf; primops = uu___112_1549.primops; do_not_unfold_pure_lets = uu___112_1549.do_not_unfold_pure_lets; unfold_until = uu___112_1549.unfold_until; unfold_only = uu___112_1549.unfold_only; unfold_fully = uu___112_1549.unfold_fully; unfold_attr = (add_opt attr fs.unfold_attr); unfold_tac = uu___112_1549.unfold_tac; pure_subterms_within_computations = uu___112_1549.pure_subterms_within_computations; simplify = uu___112_1549.simplify; erase_universes = uu___112_1549.erase_universes; allow_unbound_universes = uu___112_1549.allow_unbound_universes; reify_ = uu___112_1549.reify_; compress_uvars = uu___112_1549.compress_uvars; no_full_norm = uu___112_1549.no_full_norm; check_no_uvars = uu___112_1549.check_no_uvars; unmeta = uu___112_1549.unmeta; unascribe = uu___112_1549.unascribe; in_full_norm_request = uu___112_1549.in_full_norm_request; weakly_reduce_scrutinee = uu___112_1549.weakly_reduce_scrutinee})
end
| UnfoldTac -> begin
(

let uu___113_1550 = fs
in {beta = uu___113_1550.beta; iota = uu___113_1550.iota; zeta = uu___113_1550.zeta; weak = uu___113_1550.weak; hnf = uu___113_1550.hnf; primops = uu___113_1550.primops; do_not_unfold_pure_lets = uu___113_1550.do_not_unfold_pure_lets; unfold_until = uu___113_1550.unfold_until; unfold_only = uu___113_1550.unfold_only; unfold_fully = uu___113_1550.unfold_fully; unfold_attr = uu___113_1550.unfold_attr; unfold_tac = true; pure_subterms_within_computations = uu___113_1550.pure_subterms_within_computations; simplify = uu___113_1550.simplify; erase_universes = uu___113_1550.erase_universes; allow_unbound_universes = uu___113_1550.allow_unbound_universes; reify_ = uu___113_1550.reify_; compress_uvars = uu___113_1550.compress_uvars; no_full_norm = uu___113_1550.no_full_norm; check_no_uvars = uu___113_1550.check_no_uvars; unmeta = uu___113_1550.unmeta; unascribe = uu___113_1550.unascribe; in_full_norm_request = uu___113_1550.in_full_norm_request; weakly_reduce_scrutinee = uu___113_1550.weakly_reduce_scrutinee})
end
| PureSubtermsWithinComputations -> begin
(

let uu___114_1551 = fs
in {beta = uu___114_1551.beta; iota = uu___114_1551.iota; zeta = uu___114_1551.zeta; weak = uu___114_1551.weak; hnf = uu___114_1551.hnf; primops = uu___114_1551.primops; do_not_unfold_pure_lets = uu___114_1551.do_not_unfold_pure_lets; unfold_until = uu___114_1551.unfold_until; unfold_only = uu___114_1551.unfold_only; unfold_fully = uu___114_1551.unfold_fully; unfold_attr = uu___114_1551.unfold_attr; unfold_tac = uu___114_1551.unfold_tac; pure_subterms_within_computations = true; simplify = uu___114_1551.simplify; erase_universes = uu___114_1551.erase_universes; allow_unbound_universes = uu___114_1551.allow_unbound_universes; reify_ = uu___114_1551.reify_; compress_uvars = uu___114_1551.compress_uvars; no_full_norm = uu___114_1551.no_full_norm; check_no_uvars = uu___114_1551.check_no_uvars; unmeta = uu___114_1551.unmeta; unascribe = uu___114_1551.unascribe; in_full_norm_request = uu___114_1551.in_full_norm_request; weakly_reduce_scrutinee = uu___114_1551.weakly_reduce_scrutinee})
end
| Simplify -> begin
(

let uu___115_1552 = fs
in {beta = uu___115_1552.beta; iota = uu___115_1552.iota; zeta = uu___115_1552.zeta; weak = uu___115_1552.weak; hnf = uu___115_1552.hnf; primops = uu___115_1552.primops; do_not_unfold_pure_lets = uu___115_1552.do_not_unfold_pure_lets; unfold_until = uu___115_1552.unfold_until; unfold_only = uu___115_1552.unfold_only; unfold_fully = uu___115_1552.unfold_fully; unfold_attr = uu___115_1552.unfold_attr; unfold_tac = uu___115_1552.unfold_tac; pure_subterms_within_computations = uu___115_1552.pure_subterms_within_computations; simplify = true; erase_universes = uu___115_1552.erase_universes; allow_unbound_universes = uu___115_1552.allow_unbound_universes; reify_ = uu___115_1552.reify_; compress_uvars = uu___115_1552.compress_uvars; no_full_norm = uu___115_1552.no_full_norm; check_no_uvars = uu___115_1552.check_no_uvars; unmeta = uu___115_1552.unmeta; unascribe = uu___115_1552.unascribe; in_full_norm_request = uu___115_1552.in_full_norm_request; weakly_reduce_scrutinee = uu___115_1552.weakly_reduce_scrutinee})
end
| EraseUniverses -> begin
(

let uu___116_1553 = fs
in {beta = uu___116_1553.beta; iota = uu___116_1553.iota; zeta = uu___116_1553.zeta; weak = uu___116_1553.weak; hnf = uu___116_1553.hnf; primops = uu___116_1553.primops; do_not_unfold_pure_lets = uu___116_1553.do_not_unfold_pure_lets; unfold_until = uu___116_1553.unfold_until; unfold_only = uu___116_1553.unfold_only; unfold_fully = uu___116_1553.unfold_fully; unfold_attr = uu___116_1553.unfold_attr; unfold_tac = uu___116_1553.unfold_tac; pure_subterms_within_computations = uu___116_1553.pure_subterms_within_computations; simplify = uu___116_1553.simplify; erase_universes = true; allow_unbound_universes = uu___116_1553.allow_unbound_universes; reify_ = uu___116_1553.reify_; compress_uvars = uu___116_1553.compress_uvars; no_full_norm = uu___116_1553.no_full_norm; check_no_uvars = uu___116_1553.check_no_uvars; unmeta = uu___116_1553.unmeta; unascribe = uu___116_1553.unascribe; in_full_norm_request = uu___116_1553.in_full_norm_request; weakly_reduce_scrutinee = uu___116_1553.weakly_reduce_scrutinee})
end
| AllowUnboundUniverses -> begin
(

let uu___117_1554 = fs
in {beta = uu___117_1554.beta; iota = uu___117_1554.iota; zeta = uu___117_1554.zeta; weak = uu___117_1554.weak; hnf = uu___117_1554.hnf; primops = uu___117_1554.primops; do_not_unfold_pure_lets = uu___117_1554.do_not_unfold_pure_lets; unfold_until = uu___117_1554.unfold_until; unfold_only = uu___117_1554.unfold_only; unfold_fully = uu___117_1554.unfold_fully; unfold_attr = uu___117_1554.unfold_attr; unfold_tac = uu___117_1554.unfold_tac; pure_subterms_within_computations = uu___117_1554.pure_subterms_within_computations; simplify = uu___117_1554.simplify; erase_universes = uu___117_1554.erase_universes; allow_unbound_universes = true; reify_ = uu___117_1554.reify_; compress_uvars = uu___117_1554.compress_uvars; no_full_norm = uu___117_1554.no_full_norm; check_no_uvars = uu___117_1554.check_no_uvars; unmeta = uu___117_1554.unmeta; unascribe = uu___117_1554.unascribe; in_full_norm_request = uu___117_1554.in_full_norm_request; weakly_reduce_scrutinee = uu___117_1554.weakly_reduce_scrutinee})
end
| Reify -> begin
(

let uu___118_1555 = fs
in {beta = uu___118_1555.beta; iota = uu___118_1555.iota; zeta = uu___118_1555.zeta; weak = uu___118_1555.weak; hnf = uu___118_1555.hnf; primops = uu___118_1555.primops; do_not_unfold_pure_lets = uu___118_1555.do_not_unfold_pure_lets; unfold_until = uu___118_1555.unfold_until; unfold_only = uu___118_1555.unfold_only; unfold_fully = uu___118_1555.unfold_fully; unfold_attr = uu___118_1555.unfold_attr; unfold_tac = uu___118_1555.unfold_tac; pure_subterms_within_computations = uu___118_1555.pure_subterms_within_computations; simplify = uu___118_1555.simplify; erase_universes = uu___118_1555.erase_universes; allow_unbound_universes = uu___118_1555.allow_unbound_universes; reify_ = true; compress_uvars = uu___118_1555.compress_uvars; no_full_norm = uu___118_1555.no_full_norm; check_no_uvars = uu___118_1555.check_no_uvars; unmeta = uu___118_1555.unmeta; unascribe = uu___118_1555.unascribe; in_full_norm_request = uu___118_1555.in_full_norm_request; weakly_reduce_scrutinee = uu___118_1555.weakly_reduce_scrutinee})
end
| CompressUvars -> begin
(

let uu___119_1556 = fs
in {beta = uu___119_1556.beta; iota = uu___119_1556.iota; zeta = uu___119_1556.zeta; weak = uu___119_1556.weak; hnf = uu___119_1556.hnf; primops = uu___119_1556.primops; do_not_unfold_pure_lets = uu___119_1556.do_not_unfold_pure_lets; unfold_until = uu___119_1556.unfold_until; unfold_only = uu___119_1556.unfold_only; unfold_fully = uu___119_1556.unfold_fully; unfold_attr = uu___119_1556.unfold_attr; unfold_tac = uu___119_1556.unfold_tac; pure_subterms_within_computations = uu___119_1556.pure_subterms_within_computations; simplify = uu___119_1556.simplify; erase_universes = uu___119_1556.erase_universes; allow_unbound_universes = uu___119_1556.allow_unbound_universes; reify_ = uu___119_1556.reify_; compress_uvars = true; no_full_norm = uu___119_1556.no_full_norm; check_no_uvars = uu___119_1556.check_no_uvars; unmeta = uu___119_1556.unmeta; unascribe = uu___119_1556.unascribe; in_full_norm_request = uu___119_1556.in_full_norm_request; weakly_reduce_scrutinee = uu___119_1556.weakly_reduce_scrutinee})
end
| NoFullNorm -> begin
(

let uu___120_1557 = fs
in {beta = uu___120_1557.beta; iota = uu___120_1557.iota; zeta = uu___120_1557.zeta; weak = uu___120_1557.weak; hnf = uu___120_1557.hnf; primops = uu___120_1557.primops; do_not_unfold_pure_lets = uu___120_1557.do_not_unfold_pure_lets; unfold_until = uu___120_1557.unfold_until; unfold_only = uu___120_1557.unfold_only; unfold_fully = uu___120_1557.unfold_fully; unfold_attr = uu___120_1557.unfold_attr; unfold_tac = uu___120_1557.unfold_tac; pure_subterms_within_computations = uu___120_1557.pure_subterms_within_computations; simplify = uu___120_1557.simplify; erase_universes = uu___120_1557.erase_universes; allow_unbound_universes = uu___120_1557.allow_unbound_universes; reify_ = uu___120_1557.reify_; compress_uvars = uu___120_1557.compress_uvars; no_full_norm = true; check_no_uvars = uu___120_1557.check_no_uvars; unmeta = uu___120_1557.unmeta; unascribe = uu___120_1557.unascribe; in_full_norm_request = uu___120_1557.in_full_norm_request; weakly_reduce_scrutinee = uu___120_1557.weakly_reduce_scrutinee})
end
| CheckNoUvars -> begin
(

let uu___121_1558 = fs
in {beta = uu___121_1558.beta; iota = uu___121_1558.iota; zeta = uu___121_1558.zeta; weak = uu___121_1558.weak; hnf = uu___121_1558.hnf; primops = uu___121_1558.primops; do_not_unfold_pure_lets = uu___121_1558.do_not_unfold_pure_lets; unfold_until = uu___121_1558.unfold_until; unfold_only = uu___121_1558.unfold_only; unfold_fully = uu___121_1558.unfold_fully; unfold_attr = uu___121_1558.unfold_attr; unfold_tac = uu___121_1558.unfold_tac; pure_subterms_within_computations = uu___121_1558.pure_subterms_within_computations; simplify = uu___121_1558.simplify; erase_universes = uu___121_1558.erase_universes; allow_unbound_universes = uu___121_1558.allow_unbound_universes; reify_ = uu___121_1558.reify_; compress_uvars = uu___121_1558.compress_uvars; no_full_norm = uu___121_1558.no_full_norm; check_no_uvars = true; unmeta = uu___121_1558.unmeta; unascribe = uu___121_1558.unascribe; in_full_norm_request = uu___121_1558.in_full_norm_request; weakly_reduce_scrutinee = uu___121_1558.weakly_reduce_scrutinee})
end
| Unmeta -> begin
(

let uu___122_1559 = fs
in {beta = uu___122_1559.beta; iota = uu___122_1559.iota; zeta = uu___122_1559.zeta; weak = uu___122_1559.weak; hnf = uu___122_1559.hnf; primops = uu___122_1559.primops; do_not_unfold_pure_lets = uu___122_1559.do_not_unfold_pure_lets; unfold_until = uu___122_1559.unfold_until; unfold_only = uu___122_1559.unfold_only; unfold_fully = uu___122_1559.unfold_fully; unfold_attr = uu___122_1559.unfold_attr; unfold_tac = uu___122_1559.unfold_tac; pure_subterms_within_computations = uu___122_1559.pure_subterms_within_computations; simplify = uu___122_1559.simplify; erase_universes = uu___122_1559.erase_universes; allow_unbound_universes = uu___122_1559.allow_unbound_universes; reify_ = uu___122_1559.reify_; compress_uvars = uu___122_1559.compress_uvars; no_full_norm = uu___122_1559.no_full_norm; check_no_uvars = uu___122_1559.check_no_uvars; unmeta = true; unascribe = uu___122_1559.unascribe; in_full_norm_request = uu___122_1559.in_full_norm_request; weakly_reduce_scrutinee = uu___122_1559.weakly_reduce_scrutinee})
end
| Unascribe -> begin
(

let uu___123_1560 = fs
in {beta = uu___123_1560.beta; iota = uu___123_1560.iota; zeta = uu___123_1560.zeta; weak = uu___123_1560.weak; hnf = uu___123_1560.hnf; primops = uu___123_1560.primops; do_not_unfold_pure_lets = uu___123_1560.do_not_unfold_pure_lets; unfold_until = uu___123_1560.unfold_until; unfold_only = uu___123_1560.unfold_only; unfold_fully = uu___123_1560.unfold_fully; unfold_attr = uu___123_1560.unfold_attr; unfold_tac = uu___123_1560.unfold_tac; pure_subterms_within_computations = uu___123_1560.pure_subterms_within_computations; simplify = uu___123_1560.simplify; erase_universes = uu___123_1560.erase_universes; allow_unbound_universes = uu___123_1560.allow_unbound_universes; reify_ = uu___123_1560.reify_; compress_uvars = uu___123_1560.compress_uvars; no_full_norm = uu___123_1560.no_full_norm; check_no_uvars = uu___123_1560.check_no_uvars; unmeta = uu___123_1560.unmeta; unascribe = true; in_full_norm_request = uu___123_1560.in_full_norm_request; weakly_reduce_scrutinee = uu___123_1560.weakly_reduce_scrutinee})
end)))


let rec to_fsteps : step Prims.list  ->  fsteps = (fun s -> (FStar_List.fold_right fstep_add_one s default_steps))

type psc =
{psc_range : FStar_Range.range; psc_subst : unit  ->  FStar_Syntax_Syntax.subst_t}


let __proj__Mkpsc__item__psc_range : psc  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {psc_range = __fname__psc_range; psc_subst = __fname__psc_subst} -> begin
__fname__psc_range
end))


let __proj__Mkpsc__item__psc_subst : psc  ->  unit  ->  FStar_Syntax_Syntax.subst_t = (fun projectee -> (match (projectee) with
| {psc_range = __fname__psc_range; psc_subst = __fname__psc_subst} -> begin
__fname__psc_subst
end))


let null_psc : psc = {psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1613 -> [])}


let psc_range : psc  ->  FStar_Range.range = (fun psc -> psc.psc_range)


let psc_subst : psc  ->  FStar_Syntax_Syntax.subst_t = (fun psc -> (psc.psc_subst ()))

type primitive_step =
{name : FStar_Ident.lid; arity : Prims.int; auto_reflect : Prims.int FStar_Pervasives_Native.option; strong_reduction_ok : Prims.bool; requires_binder_substitution : Prims.bool; interpretation : psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option}


let __proj__Mkprimitive_step__item__name : primitive_step  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; auto_reflect = __fname__auto_reflect; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__name
end))


let __proj__Mkprimitive_step__item__arity : primitive_step  ->  Prims.int = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; auto_reflect = __fname__auto_reflect; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__arity
end))


let __proj__Mkprimitive_step__item__auto_reflect : primitive_step  ->  Prims.int FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; auto_reflect = __fname__auto_reflect; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__auto_reflect
end))


let __proj__Mkprimitive_step__item__strong_reduction_ok : primitive_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; auto_reflect = __fname__auto_reflect; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__strong_reduction_ok
end))


let __proj__Mkprimitive_step__item__requires_binder_substitution : primitive_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; auto_reflect = __fname__auto_reflect; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__requires_binder_substitution
end))


let __proj__Mkprimitive_step__item__interpretation : primitive_step  ->  psc  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {name = __fname__name; arity = __fname__arity; auto_reflect = __fname__auto_reflect; strong_reduction_ok = __fname__strong_reduction_ok; requires_binder_substitution = __fname__requires_binder_substitution; interpretation = __fname__interpretation} -> begin
__fname__interpretation
end))

type closure =
| Clos of ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool)
| Univ of FStar_Syntax_Syntax.universe
| Dummy


let uu___is_Clos : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Clos (_0) -> begin
true
end
| uu____1926 -> begin
false
end))


let __proj__Clos__item___0 : closure  ->  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool) = (fun projectee -> (match (projectee) with
| Clos (_0) -> begin
_0
end))


let uu___is_Univ : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Univ (_0) -> begin
true
end
| uu____2030 -> begin
false
end))


let __proj__Univ__item___0 : closure  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| Univ (_0) -> begin
_0
end))


let uu___is_Dummy : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Dummy -> begin
true
end
| uu____2043 -> begin
false
end))


type env =
(FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list


let dummy : (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) = ((FStar_Pervasives_Native.None), (Dummy))

type debug_switches =
{gen : Prims.bool; primop : Prims.bool; b380 : Prims.bool; wpe : Prims.bool; norm_delayed : Prims.bool; print_normalized : Prims.bool}


let __proj__Mkdebug_switches__item__gen : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380; wpe = __fname__wpe; norm_delayed = __fname__norm_delayed; print_normalized = __fname__print_normalized} -> begin
__fname__gen
end))


let __proj__Mkdebug_switches__item__primop : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380; wpe = __fname__wpe; norm_delayed = __fname__norm_delayed; print_normalized = __fname__print_normalized} -> begin
__fname__primop
end))


let __proj__Mkdebug_switches__item__b380 : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380; wpe = __fname__wpe; norm_delayed = __fname__norm_delayed; print_normalized = __fname__print_normalized} -> begin
__fname__b380
end))


let __proj__Mkdebug_switches__item__wpe : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380; wpe = __fname__wpe; norm_delayed = __fname__norm_delayed; print_normalized = __fname__print_normalized} -> begin
__fname__wpe
end))


let __proj__Mkdebug_switches__item__norm_delayed : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380; wpe = __fname__wpe; norm_delayed = __fname__norm_delayed; print_normalized = __fname__print_normalized} -> begin
__fname__norm_delayed
end))


let __proj__Mkdebug_switches__item__print_normalized : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = __fname__gen; primop = __fname__primop; b380 = __fname__b380; wpe = __fname__wpe; norm_delayed = __fname__norm_delayed; print_normalized = __fname__print_normalized} -> begin
__fname__print_normalized
end))

type cfg =
{steps : fsteps; tcenv : FStar_TypeChecker_Env.env; debug : debug_switches; delta_level : FStar_TypeChecker_Env.delta_level Prims.list; primitive_steps : primitive_step FStar_Util.psmap; strong : Prims.bool; memoize_lazy : Prims.bool; normalize_pure_lets : Prims.bool}


let __proj__Mkcfg__item__steps : cfg  ->  fsteps = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; debug = __fname__debug; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps; strong = __fname__strong; memoize_lazy = __fname__memoize_lazy; normalize_pure_lets = __fname__normalize_pure_lets} -> begin
__fname__steps
end))


let __proj__Mkcfg__item__tcenv : cfg  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; debug = __fname__debug; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps; strong = __fname__strong; memoize_lazy = __fname__memoize_lazy; normalize_pure_lets = __fname__normalize_pure_lets} -> begin
__fname__tcenv
end))


let __proj__Mkcfg__item__debug : cfg  ->  debug_switches = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; debug = __fname__debug; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps; strong = __fname__strong; memoize_lazy = __fname__memoize_lazy; normalize_pure_lets = __fname__normalize_pure_lets} -> begin
__fname__debug
end))


let __proj__Mkcfg__item__delta_level : cfg  ->  FStar_TypeChecker_Env.delta_level Prims.list = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; debug = __fname__debug; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps; strong = __fname__strong; memoize_lazy = __fname__memoize_lazy; normalize_pure_lets = __fname__normalize_pure_lets} -> begin
__fname__delta_level
end))


let __proj__Mkcfg__item__primitive_steps : cfg  ->  primitive_step FStar_Util.psmap = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; debug = __fname__debug; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps; strong = __fname__strong; memoize_lazy = __fname__memoize_lazy; normalize_pure_lets = __fname__normalize_pure_lets} -> begin
__fname__primitive_steps
end))


let __proj__Mkcfg__item__strong : cfg  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; debug = __fname__debug; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps; strong = __fname__strong; memoize_lazy = __fname__memoize_lazy; normalize_pure_lets = __fname__normalize_pure_lets} -> begin
__fname__strong
end))


let __proj__Mkcfg__item__memoize_lazy : cfg  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; debug = __fname__debug; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps; strong = __fname__strong; memoize_lazy = __fname__memoize_lazy; normalize_pure_lets = __fname__normalize_pure_lets} -> begin
__fname__memoize_lazy
end))


let __proj__Mkcfg__item__normalize_pure_lets : cfg  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {steps = __fname__steps; tcenv = __fname__tcenv; debug = __fname__debug; delta_level = __fname__delta_level; primitive_steps = __fname__primitive_steps; strong = __fname__strong; memoize_lazy = __fname__memoize_lazy; normalize_pure_lets = __fname__normalize_pure_lets} -> begin
__fname__normalize_pure_lets
end))


let add_steps : primitive_step FStar_Util.psmap  ->  primitive_step Prims.list  ->  primitive_step FStar_Util.psmap = (fun m l -> (FStar_List.fold_right (fun p m1 -> (

let uu____2375 = (FStar_Ident.text_of_lid p.name)
in (FStar_Util.psmap_add m1 uu____2375 p))) l m))


let prim_from_list : primitive_step Prims.list  ->  primitive_step FStar_Util.psmap = (fun l -> (

let uu____2389 = (FStar_Util.psmap_empty ())
in (add_steps uu____2389 l)))


let find_prim_step : cfg  ->  FStar_Syntax_Syntax.fv  ->  primitive_step FStar_Pervasives_Native.option = (fun cfg fv -> (

let uu____2404 = (FStar_Ident.text_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.psmap_try_find cfg.primitive_steps uu____2404)))


type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list

type stack_elt =
| Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
| MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
| Match of (env * branches * cfg * FStar_Range.range)
| Abs of (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option * FStar_Range.range)
| App of (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| Meta of (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)
| Let of (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range)
| Cfg of cfg
| Debug of (FStar_Syntax_Syntax.term * FStar_Util.time)


let uu___is_Arg : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Arg (_0) -> begin
true
end
| uu____2610 -> begin
false
end))


let __proj__Arg__item___0 : stack_elt  ->  (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Arg (_0) -> begin
_0
end))


let uu___is_UnivArgs : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnivArgs (_0) -> begin
true
end
| uu____2648 -> begin
false
end))


let __proj__UnivArgs__item___0 : stack_elt  ->  (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| UnivArgs (_0) -> begin
_0
end))


let uu___is_MemoLazy : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MemoLazy (_0) -> begin
true
end
| uu____2686 -> begin
false
end))


let __proj__MemoLazy__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo = (fun projectee -> (match (projectee) with
| MemoLazy (_0) -> begin
_0
end))


let uu___is_Match : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Match (_0) -> begin
true
end
| uu____2831 -> begin
false
end))


let __proj__Match__item___0 : stack_elt  ->  (env * branches * cfg * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Match (_0) -> begin
_0
end))


let uu___is_Abs : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Abs (_0) -> begin
true
end
| uu____2881 -> begin
false
end))


let __proj__Abs__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Abs (_0) -> begin
_0
end))


let uu___is_App : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| App (_0) -> begin
true
end
| uu____2939 -> begin
false
end))


let __proj__App__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| App (_0) -> begin
_0
end))


let uu___is_Meta : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta (_0) -> begin
true
end
| uu____2983 -> begin
false
end))


let __proj__Meta__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.metadata * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Meta (_0) -> begin
_0
end))


let uu___is_Let : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
true
end
| uu____3023 -> begin
false
end))


let __proj__Let__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
_0
end))


let uu___is_Cfg : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Cfg (_0) -> begin
true
end
| uu____3061 -> begin
false
end))


let __proj__Cfg__item___0 : stack_elt  ->  cfg = (fun projectee -> (match (projectee) with
| Cfg (_0) -> begin
_0
end))


let uu___is_Debug : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Debug (_0) -> begin
true
end
| uu____3079 -> begin
false
end))


let __proj__Debug__item___0 : stack_elt  ->  (FStar_Syntax_Syntax.term * FStar_Util.time) = (fun projectee -> (match (projectee) with
| Debug (_0) -> begin
_0
end))


type stack =
stack_elt Prims.list


let head_of : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____3106 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____3106) with
| (hd1, uu____3120) -> begin
hd1
end)))


let mk : 'Auu____3143 . 'Auu____3143  ->  FStar_Range.range  ->  'Auu____3143 FStar_Syntax_Syntax.syntax = (fun t r -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r))


let set_memo : 'a . cfg  ->  'a FStar_Syntax_Syntax.memo  ->  'a  ->  unit = (fun cfg r t -> (match (cfg.memoize_lazy) with
| true -> begin
(

let uu____3254 = (FStar_ST.op_Bang r)
in (match (uu____3254) with
| FStar_Pervasives_Native.Some (uu____3360) -> begin
(failwith "Unexpected set_memo: thunk already evaluated")
end
| FStar_Pervasives_Native.None -> begin
(FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some (t)))
end))
end
| uu____3464 -> begin
()
end))


let rec env_to_string : (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list  ->  Prims.string = (fun env -> (

let uu____3490 = (FStar_List.map (fun uu____3504 -> (match (uu____3504) with
| (bopt, c) -> begin
(

let uu____3517 = (match (bopt) with
| FStar_Pervasives_Native.None -> begin
"."
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_Print.binder_to_string x)
end)
in (

let uu____3519 = (closure_to_string c)
in (FStar_Util.format2 "(%s, %s)" uu____3517 uu____3519)))
end)) env)
in (FStar_All.pipe_right uu____3490 (FStar_String.concat "; "))))
and closure_to_string : closure  ->  Prims.string = (fun uu___82_3522 -> (match (uu___82_3522) with
| Clos (env, t, uu____3525, uu____3526) -> begin
(

let uu____3571 = (FStar_All.pipe_right (FStar_List.length env) FStar_Util.string_of_int)
in (

let uu____3578 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "(env=%s elts; %s)" uu____3571 uu____3578)))
end
| Univ (uu____3579) -> begin
"Univ"
end
| Dummy -> begin
"dummy"
end))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun uu___83_3584 -> (match (uu___83_3584) with
| Arg (c, uu____3586, uu____3587) -> begin
(

let uu____3588 = (closure_to_string c)
in (FStar_Util.format1 "Closure %s" uu____3588))
end
| MemoLazy (uu____3589) -> begin
"MemoLazy"
end
| Abs (uu____3596, bs, uu____3598, uu____3599, uu____3600) -> begin
(

let uu____3605 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" uu____3605))
end
| UnivArgs (uu____3610) -> begin
"UnivArgs"
end
| Match (uu____3617) -> begin
"Match"
end
| App (uu____3626, t, uu____3628, uu____3629) -> begin
(

let uu____3630 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "App %s" uu____3630))
end
| Meta (uu____3631, m, uu____3633) -> begin
"Meta"
end
| Let (uu____3634) -> begin
"Let"
end
| Cfg (uu____3643) -> begin
"Cfg"
end
| Debug (t, uu____3645) -> begin
(

let uu____3646 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Debug %s" uu____3646))
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (

let uu____3656 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right uu____3656 (FStar_String.concat "; "))))


let log : cfg  ->  (unit  ->  unit)  ->  unit = (fun cfg f -> (match (cfg.debug.gen) with
| true -> begin
(f ())
end
| uu____3676 -> begin
()
end))


let log_primops : cfg  ->  (unit  ->  unit)  ->  unit = (fun cfg f -> (match (cfg.debug.primop) with
| true -> begin
(f ())
end
| uu____3692 -> begin
()
end))


let is_empty : 'Auu____3697 . 'Auu____3697 Prims.list  ->  Prims.bool = (fun uu___84_3704 -> (match (uu___84_3704) with
| [] -> begin
true
end
| uu____3707 -> begin
false
end))


let lookup_bvar : (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.bv  ->  closure = (fun env x -> (FStar_All.try_with (fun uu___125_3738 -> (match (()) with
| () -> begin
(

let uu____3739 = (FStar_List.nth env x.FStar_Syntax_Syntax.index)
in (FStar_Pervasives_Native.snd uu____3739))
end)) (fun uu___124_3757 -> (match (uu___124_3757) with
| uu____3758 -> begin
(

let uu____3759 = (

let uu____3760 = (FStar_Syntax_Print.db_to_string x)
in (

let uu____3761 = (env_to_string env)
in (FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____3760 uu____3761)))
in (failwith uu____3759))
end))))


let downgrade_ghost_effect_name : FStar_Ident.lident  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun l -> (

let uu____3769 = (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid)
in (match (uu____3769) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Pure_lid)
end
| uu____3772 -> begin
(

let uu____3773 = (FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid)
in (match (uu____3773) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_Tot_lid)
end
| uu____3776 -> begin
(

let uu____3777 = (FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid)
in (match (uu____3777) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.effect_PURE_lid)
end
| uu____3780 -> begin
FStar_Pervasives_Native.None
end))
end))
end)))


let norm_universe : cfg  ->  env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us1 = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let uu____3811 = (FStar_List.fold_left (fun uu____3837 u1 -> (match (uu____3837) with
| (cur_kernel, cur_max, out) -> begin
(

let uu____3862 = (FStar_Syntax_Util.univ_kernel u1)
in (match (uu____3862) with
| (k_u, n1) -> begin
(

let uu____3877 = (FStar_Syntax_Util.eq_univs cur_kernel k_u)
in (match (uu____3877) with
| true -> begin
((cur_kernel), (u1), (out))
end
| uu____3888 -> begin
((k_u), (u1), ((cur_max)::out))
end))
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us1)
in (match (uu____3811) with
| (uu____3895, u1, out) -> begin
(FStar_List.rev ((u1)::out))
end))))
in (

let rec aux = (fun u1 -> (

let u2 = (FStar_Syntax_Subst.compress_univ u1)
in (match (u2) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(FStar_All.try_with (fun uu___127_3919 -> (match (()) with
| () -> begin
(

let uu____3922 = (

let uu____3923 = (FStar_List.nth env x)
in (FStar_Pervasives_Native.snd uu____3923))
in (match (uu____3922) with
| Univ (u3) -> begin
(aux u3)
end
| Dummy -> begin
(u2)::[]
end
| uu____3941 -> begin
(failwith "Impossible: universe variable bound to a term")
end))
end)) (fun uu___126_3946 -> (match (uu___126_3946) with
| uu____3949 -> begin
(match (cfg.steps.allow_unbound_universes) with
| true -> begin
(FStar_Syntax_Syntax.U_unknown)::[]
end
| uu____3952 -> begin
(failwith "Universe variable not found")
end)
end)))
end
| FStar_Syntax_Syntax.U_unif (uu____3955) when cfg.steps.check_no_uvars -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_zero -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_unif (uu____3964) -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_name (uu____3973) -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_unknown -> begin
(u2)::[]
end
| FStar_Syntax_Syntax.U_max ([]) -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let us1 = (

let uu____3980 = (FStar_List.collect aux us)
in (FStar_All.pipe_right uu____3980 norm_univs))
in (match (us1) with
| (u_k)::(hd1)::rest -> begin
(

let rest1 = (hd1)::rest
in (

let uu____3997 = (FStar_Syntax_Util.univ_kernel u_k)
in (match (uu____3997) with
| (FStar_Syntax_Syntax.U_zero, n1) -> begin
(

let uu____4005 = (FStar_All.pipe_right rest1 (FStar_List.for_all (fun u3 -> (

let uu____4013 = (FStar_Syntax_Util.univ_kernel u3)
in (match (uu____4013) with
| (uu____4018, m) -> begin
(n1 <= m)
end)))))
in (match (uu____4005) with
| true -> begin
rest1
end
| uu____4022 -> begin
us1
end))
end
| uu____4023 -> begin
us1
end)))
end
| uu____4028 -> begin
us1
end))
end
| FStar_Syntax_Syntax.U_succ (u3) -> begin
(

let uu____4032 = (aux u3)
in (FStar_List.map (fun _0_17 -> FStar_Syntax_Syntax.U_succ (_0_17)) uu____4032))
end)))
in (match (cfg.steps.erase_universes) with
| true -> begin
FStar_Syntax_Syntax.U_unknown
end
| uu____4035 -> begin
(

let uu____4036 = (aux u)
in (match (uu____4036) with
| [] -> begin
FStar_Syntax_Syntax.U_zero
end
| (FStar_Syntax_Syntax.U_zero)::[] -> begin
FStar_Syntax_Syntax.U_zero
end
| (FStar_Syntax_Syntax.U_zero)::(u1)::[] -> begin
u1
end
| (FStar_Syntax_Syntax.U_zero)::us -> begin
FStar_Syntax_Syntax.U_max (us)
end
| (u1)::[] -> begin
u1
end
| us -> begin
FStar_Syntax_Syntax.U_max (us)
end))
end))))


let rec inline_closure_env : cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun cfg env stack t -> ((log cfg (fun uu____4182 -> (

let uu____4183 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____4184 = (env_to_string env)
in (

let uu____4185 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n" uu____4183 uu____4184 uu____4185))))));
(match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation cfg.steps.compress_uvars) -> begin
(rebuild_closure cfg env stack t)
end
| uu____4194 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____4197) -> begin
(

let uu____4222 = (FStar_Syntax_Subst.compress t)
in (inline_closure_env cfg env stack uu____4222))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_constant (uu____4223) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_name (uu____4224) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_lazy (uu____4225) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____4226) -> begin
(rebuild_closure cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_uvar (uu____4227) -> begin
(match (cfg.steps.check_no_uvars) with
| true -> begin
(

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____4249) -> begin
(

let uu____4266 = (

let uu____4267 = (FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos)
in (

let uu____4268 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format2 "(%s): CheckNoUvars: Unexpected unification variable remains: %s" uu____4267 uu____4268)))
in (failwith uu____4266))
end
| uu____4271 -> begin
(inline_closure_env cfg env stack t1)
end))
end
| uu____4272 -> begin
(rebuild_closure cfg env stack t)
end)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let t1 = (

let uu____4277 = (

let uu____4278 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (uu____4278))
in (mk uu____4277 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg env stack t1))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let t1 = (

let uu____4286 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t' uu____4286))
in (rebuild_closure cfg env stack t1))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____4288 = (lookup_bvar env x)
in (match (uu____4288) with
| Univ (uu____4291) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(

let x1 = (

let uu___128_4295 = x
in {FStar_Syntax_Syntax.ppname = uu___128_4295.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___128_4295.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun})
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_bvar (x1)) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env stack t1)))
end
| Clos (env1, t0, uu____4301, uu____4302) -> begin
(inline_closure_env cfg env1 stack t0)
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let stack1 = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____4387 stack1 -> (match (uu____4387) with
| (a, aq) -> begin
(

let uu____4399 = (

let uu____4400 = (

let uu____4407 = (

let uu____4408 = (

let uu____4439 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____4439), (false)))
in Clos (uu____4408))
in ((uu____4407), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (uu____4400))
in (uu____4399)::stack1)
end)) args))
in (inline_closure_env cfg env stack1 head1))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let env' = (FStar_All.pipe_right env (FStar_List.fold_right (fun _b env1 -> (((FStar_Pervasives_Native.None), (Dummy)))::env1) bs))
in (

let stack1 = (Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack
in (inline_closure_env cfg env' stack1 body)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____4681 = (close_binders cfg env bs)
in (match (uu____4681) with
| (bs1, env') -> begin
(

let c1 = (close_comp cfg env' c)
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_arrow (((bs1), (c1)))) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env stack t1)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____4728 = (

let uu____4739 = (

let uu____4746 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4746)::[])
in (close_binders cfg env uu____4739))
in (match (uu____4728) with
| (x1, env1) -> begin
(

let phi1 = (non_tail_inline_closure_env cfg env1 phi)
in (

let t1 = (

let uu____4769 = (

let uu____4770 = (

let uu____4777 = (

let uu____4778 = (FStar_List.hd x1)
in (FStar_All.pipe_right uu____4778 FStar_Pervasives_Native.fst))
in ((uu____4777), (phi1)))
in FStar_Syntax_Syntax.Tm_refine (uu____4770))
in (mk uu____4769 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg env1 stack t1)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, (annot, tacopt), lopt) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t2) -> begin
(

let uu____4869 = (non_tail_inline_closure_env cfg env t2)
in FStar_Util.Inl (uu____4869))
end
| FStar_Util.Inr (c) -> begin
(

let uu____4883 = (close_comp cfg env c)
in FStar_Util.Inr (uu____4883))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (non_tail_inline_closure_env cfg env))
in (

let t2 = (

let uu____4902 = (

let uu____4903 = (

let uu____4930 = (non_tail_inline_closure_env cfg env t1)
in ((uu____4930), (((annot1), (tacopt1))), (lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____4903))
in (mk uu____4902 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg env stack t2))))
end
| FStar_Syntax_Syntax.Tm_quoted (t', qi) -> begin
(

let t1 = (match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let uu____4976 = (

let uu____4977 = (

let uu____4984 = (non_tail_inline_closure_env cfg env t')
in ((uu____4984), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____4977))
in (mk uu____4976 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Quote_static -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted (non_tail_inline_closure_env cfg env) qi)
in (mk (FStar_Syntax_Syntax.Tm_quoted (((t'), (qi1)))) t.FStar_Syntax_Syntax.pos))
end)
in (rebuild_closure cfg env stack t1))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(

let stack1 = (Meta (((env), (m), (t.FStar_Syntax_Syntax.pos))))::stack
in (inline_closure_env cfg env stack1 t'))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env1 = (FStar_List.fold_left (fun env1 uu____5036 -> (dummy)::env1) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (non_tail_inline_closure_env cfg env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (non_tail_inline_closure_env cfg env1 lb.FStar_Syntax_Syntax.lbdef)
in (

let uu____5057 = (

let uu____5068 = (FStar_Syntax_Syntax.is_top_level ((lb)::[]))
in (match (uu____5068) with
| true -> begin
((lb.FStar_Syntax_Syntax.lbname), (body))
end
| uu____5085 -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (

let uu____5087 = (non_tail_inline_closure_env cfg ((dummy)::env0) body)
in ((FStar_Util.Inl ((

let uu___129_5103 = x
in {FStar_Syntax_Syntax.ppname = uu___129_5103.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___129_5103.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = typ}))), (uu____5087))))
end))
in (match (uu____5057) with
| (nm, body1) -> begin
(

let lb1 = (

let uu___130_5121 = lb
in {FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = uu___130_5121.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = uu___130_5121.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu___130_5121.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___130_5121.FStar_Syntax_Syntax.lbpos})
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb1)::[]))), (body1)))) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env0 stack t1)))
end))))))
end
| FStar_Syntax_Syntax.Tm_let ((uu____5135, lbs), body) -> begin
(

let norm_one_lb = (fun env1 lb -> (

let env_univs = (FStar_List.fold_right (fun uu____5198 env2 -> (dummy)::env2) lb.FStar_Syntax_Syntax.lbunivs env1)
in (

let env2 = (

let uu____5223 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5223) with
| true -> begin
env_univs
end
| uu____5232 -> begin
(FStar_List.fold_right (fun uu____5243 env2 -> (dummy)::env2) lbs env_univs)
end))
in (

let ty = (non_tail_inline_closure_env cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (

let nm = (

let uu____5267 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____5267) with
| true -> begin
lb.FStar_Syntax_Syntax.lbname
end
| uu____5272 -> begin
(

let x = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in FStar_Util.Inl ((

let uu___131_5275 = x
in {FStar_Syntax_Syntax.ppname = uu___131_5275.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___131_5275.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})))
end))
in (

let uu___132_5276 = lb
in (

let uu____5277 = (non_tail_inline_closure_env cfg env2 lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = uu___132_5276.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___132_5276.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5277; FStar_Syntax_Syntax.lbattrs = uu___132_5276.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___132_5276.FStar_Syntax_Syntax.lbpos})))))))
in (

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body1 = (

let body_env = (FStar_List.fold_right (fun uu____5309 env1 -> (dummy)::env1) lbs1 env)
in (non_tail_inline_closure_env cfg body_env body))
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs1))), (body1)))) t.FStar_Syntax_Syntax.pos)
in (rebuild_closure cfg env stack t1)))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let stack1 = (Match (((env), (branches), (cfg), (t.FStar_Syntax_Syntax.pos))))::stack
in (inline_closure_env cfg env stack1 head1))
end)
end);
))
and non_tail_inline_closure_env : cfg  ->  env  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun cfg env t -> (inline_closure_env cfg env [] t))
and rebuild_closure : cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun cfg env stack t -> ((log cfg (fun uu____5412 -> (

let uu____5413 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____5414 = (env_to_string env)
in (

let uu____5415 = (stack_to_string stack)
in (

let uu____5416 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print4 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n" uu____5413 uu____5414 uu____5415 uu____5416)))))));
(match (stack) with
| [] -> begin
t
end
| (Arg (Clos (env_arg, tm, uu____5421, uu____5422), aq, r))::stack1 -> begin
(

let stack2 = (App (((env), (t), (aq), (r))))::stack1
in (inline_closure_env cfg env_arg stack2 tm))
end
| (App (env1, head1, aq, r))::stack1 -> begin
(

let t1 = (FStar_Syntax_Syntax.extend_app head1 ((t), (aq)) FStar_Pervasives_Native.None r)
in (rebuild_closure cfg env1 stack1 t1))
end
| (Abs (env', bs, env'', lopt, r))::stack1 -> begin
(

let uu____5497 = (close_binders cfg env' bs)
in (match (uu____5497) with
| (bs1, uu____5511) -> begin
(

let lopt1 = (close_lcomp_opt cfg env'' lopt)
in (

let uu____5527 = (

let uu___133_5528 = (FStar_Syntax_Util.abs bs1 t lopt1)
in {FStar_Syntax_Syntax.n = uu___133_5528.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___133_5528.FStar_Syntax_Syntax.vars})
in (rebuild_closure cfg env stack1 uu____5527)))
end))
end
| (Match (env1, branches, cfg1, r))::stack1 -> begin
(

let close_one_branch = (fun env2 uu____5574 -> (match (uu____5574) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env3 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____5649) -> begin
((p), (env3))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____5670 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____5730 uu____5731 -> (match (((uu____5730), (uu____5731))) with
| ((pats1, env4), (p1, b)) -> begin
(

let uu____5822 = (norm_pat env4 p1)
in (match (uu____5822) with
| (p2, env5) -> begin
(((((p2), (b)))::pats1), (env5))
end))
end)) (([]), (env3))))
in (match (uu____5670) with
| (pats1, env4) -> begin
(((

let uu___134_5904 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___134_5904.FStar_Syntax_Syntax.p})), (env4))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___135_5923 = x
in (

let uu____5924 = (non_tail_inline_closure_env cfg1 env3 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___135_5923.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___135_5923.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5924}))
in (((

let uu___136_5938 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___136_5938.FStar_Syntax_Syntax.p})), ((dummy)::env3)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___137_5949 = x
in (

let uu____5950 = (non_tail_inline_closure_env cfg1 env3 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___137_5949.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___137_5949.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5950}))
in (((

let uu___138_5964 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___138_5964.FStar_Syntax_Syntax.p})), ((dummy)::env3)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t1) -> begin
(

let x1 = (

let uu___139_5980 = x
in (

let uu____5981 = (non_tail_inline_closure_env cfg1 env3 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___139_5980.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___139_5980.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5981}))
in (

let t2 = (non_tail_inline_closure_env cfg1 env3 t1)
in (((

let uu___140_5990 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t2))); FStar_Syntax_Syntax.p = uu___140_5990.FStar_Syntax_Syntax.p})), (env3))))
end))
in (

let uu____5995 = (norm_pat env2 pat)
in (match (uu____5995) with
| (pat1, env3) -> begin
(

let w_opt1 = (match (w_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____6040 = (non_tail_inline_closure_env cfg1 env3 w)
in FStar_Pervasives_Native.Some (uu____6040))
end)
in (

let tm1 = (non_tail_inline_closure_env cfg1 env3 tm)
in ((pat1), (w_opt1), (tm1))))
end)))
end))
in (

let t1 = (

let uu____6059 = (

let uu____6060 = (

let uu____6083 = (FStar_All.pipe_right branches (FStar_List.map (close_one_branch env1)))
in ((t), (uu____6083)))
in FStar_Syntax_Syntax.Tm_match (uu____6060))
in (mk uu____6059 t.FStar_Syntax_Syntax.pos))
in (rebuild_closure cfg1 env1 stack1 t1)))
end
| (Meta (env_m, m, r))::stack1 -> begin
(

let m1 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let uu____6178 = (FStar_All.pipe_right args (FStar_List.map (fun args1 -> (FStar_All.pipe_right args1 (FStar_List.map (fun uu____6267 -> (match (uu____6267) with
| (a, q) -> begin
(

let uu____6286 = (non_tail_inline_closure_env cfg env_m a)
in ((uu____6286), (q)))
end)))))))
in FStar_Syntax_Syntax.Meta_pattern (uu____6178))
end
| FStar_Syntax_Syntax.Meta_monadic (m1, tbody) -> begin
(

let uu____6297 = (

let uu____6304 = (non_tail_inline_closure_env cfg env_m tbody)
in ((m1), (uu____6304)))
in FStar_Syntax_Syntax.Meta_monadic (uu____6297))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody) -> begin
(

let uu____6316 = (

let uu____6325 = (non_tail_inline_closure_env cfg env_m tbody)
in ((m1), (m2), (uu____6325)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____6316))
end
| uu____6330 -> begin
m
end)
in (

let t1 = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m1)))) r)
in (rebuild_closure cfg env stack1 t1)))
end
| uu____6334 -> begin
(failwith "Impossible: unexpected stack element")
end);
))
and close_binders : cfg  ->  env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * env) = (fun cfg env bs -> (

let uu____6348 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____6397 uu____6398 -> (match (((uu____6397), (uu____6398))) with
| ((env1, out), (b, imp)) -> begin
(

let b1 = (

let uu___141_6468 = b
in (

let uu____6469 = (inline_closure_env cfg env1 [] b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___141_6468.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___141_6468.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____6469}))
in (

let env2 = (dummy)::env1
in ((env2), ((((b1), (imp)))::out))))
end)) ((env), ([]))))
in (match (uu____6348) with
| (env1, bs1) -> begin
(((FStar_List.rev bs1)), (env1))
end)))
and close_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation cfg.steps.compress_uvars) -> begin
c
end
| uu____6562 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____6575 = (inline_closure_env cfg env [] t)
in (

let uu____6576 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' uu____6575 uu____6576)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____6589 = (inline_closure_env cfg env [] t)
in (

let uu____6590 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' uu____6589 uu____6590)))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let rt = (inline_closure_env cfg env [] c1.FStar_Syntax_Syntax.result_typ)
in (

let args = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun uu____6636 -> (match (uu____6636) with
| (a, q) -> begin
(

let uu____6649 = (inline_closure_env cfg env [] a)
in ((uu____6649), (q)))
end))))
in (

let flags1 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___85_6664 -> (match (uu___85_6664) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____6668 = (inline_closure_env cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____6668))
end
| f -> begin
f
end))))
in (

let uu____6672 = (

let uu___142_6673 = c1
in (

let uu____6674 = (FStar_List.map (norm_universe cfg env) c1.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = uu____6674; FStar_Syntax_Syntax.effect_name = uu___142_6673.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags1}))
in (FStar_Syntax_Syntax.mk_Comp uu____6672)))))
end)
end))
and filter_out_lcomp_cflags : FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun flags1 -> (FStar_All.pipe_right flags1 (FStar_List.filter (fun uu___86_6684 -> (match (uu___86_6684) with
| FStar_Syntax_Syntax.DECREASES (uu____6685) -> begin
false
end
| uu____6688 -> begin
true
end)))))
and close_lcomp_opt : cfg  ->  env  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags1 = (FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags (FStar_List.filter (fun uu___87_6706 -> (match (uu___87_6706) with
| FStar_Syntax_Syntax.DECREASES (uu____6707) -> begin
false
end
| uu____6710 -> begin
true
end))))
in (

let rc1 = (

let uu___143_6712 = rc
in (

let uu____6713 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inline_closure_env cfg env []))
in {FStar_Syntax_Syntax.residual_effect = uu___143_6712.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____6713; FStar_Syntax_Syntax.residual_flags = flags1}))
in FStar_Pervasives_Native.Some (rc1)))
end
| uu____6722 -> begin
lopt
end))


let closure_as_term : cfg  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (non_tail_inline_closure_env cfg env t))


let built_in_primitive_steps : primitive_step FStar_Util.psmap = (

let arg_as_int = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_int)))
in (

let arg_as_bool = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_bool)))
in (

let arg_as_char = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_char)))
in (

let arg_as_string = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_string)))
in (

let arg_as_list = (fun e a -> (

let uu____6835 = (

let uu____6844 = (FStar_Syntax_Embeddings.e_list e)
in (FStar_Syntax_Embeddings.try_unembed uu____6844))
in (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6835)))
in (

let arg_as_bounded_int = (fun uu____6870 -> (match (uu____6870) with
| (a, uu____6882) -> begin
(

let uu____6889 = (

let uu____6890 = (FStar_Syntax_Subst.compress a)
in uu____6890.FStar_Syntax_Syntax.n)
in (match (uu____6889) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv1); FStar_Syntax_Syntax.pos = uu____6900; FStar_Syntax_Syntax.vars = uu____6901}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, FStar_Pervasives_Native.None)); FStar_Syntax_Syntax.pos = uu____6903; FStar_Syntax_Syntax.vars = uu____6904}, uu____6905))::[]) when (

let uu____6944 = (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.ends_with uu____6944 "int_to_t")) -> begin
(

let uu____6945 = (

let uu____6950 = (FStar_BigInt.big_int_of_string i)
in ((fv1), (uu____6950)))
in FStar_Pervasives_Native.Some (uu____6945))
end
| uu____6955 -> begin
FStar_Pervasives_Native.None
end))
end))
in (

let lift_unary = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a))::[] -> begin
(

let uu____7003 = (f a)
in FStar_Pervasives_Native.Some (uu____7003))
end
| uu____7004 -> begin
FStar_Pervasives_Native.None
end))
in (

let lift_binary = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a0))::(FStar_Pervasives_Native.Some (a1))::[] -> begin
(

let uu____7060 = (f a0 a1)
in FStar_Pervasives_Native.Some (uu____7060))
end
| uu____7061 -> begin
FStar_Pervasives_Native.None
end))
in (

let unary_op = (fun as_a f res args -> (

let uu____7119 = (FStar_List.map as_a args)
in (lift_unary (f res.psc_range) uu____7119)))
in (

let binary_op = (fun as_a f res args -> (

let uu____7184 = (FStar_List.map as_a args)
in (lift_binary (f res.psc_range) uu____7184)))
in (

let as_primitive_step = (fun is_strong uu____7215 -> (match (uu____7215) with
| (l, arity, f) -> begin
{name = l; arity = arity; auto_reflect = FStar_Pervasives_Native.None; strong_reduction_ok = is_strong; requires_binder_substitution = false; interpretation = f}
end))
in (

let unary_int_op = (fun f -> (unary_op arg_as_int (fun r x -> (

let uu____7275 = (f x)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r uu____7275)))))
in (

let binary_int_op = (fun f -> (binary_op arg_as_int (fun r x y -> (

let uu____7311 = (f x y)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r uu____7311)))))
in (

let unary_bool_op = (fun f -> (unary_op arg_as_bool (fun r x -> (

let uu____7340 = (f x)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r uu____7340)))))
in (

let binary_bool_op = (fun f -> (binary_op arg_as_bool (fun r x y -> (

let uu____7376 = (f x y)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r uu____7376)))))
in (

let binary_string_op = (fun f -> (binary_op arg_as_string (fun r x y -> (

let uu____7412 = (f x y)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string r uu____7412)))))
in (

let mixed_binary_op = (fun as_a as_b embed_c f res args -> (match (args) with
| (a)::(b)::[] -> begin
(

let uu____7544 = (

let uu____7553 = (as_a a)
in (

let uu____7556 = (as_b b)
in ((uu____7553), (uu____7556))))
in (match (uu____7544) with
| (FStar_Pervasives_Native.Some (a1), FStar_Pervasives_Native.Some (b1)) -> begin
(

let uu____7571 = (

let uu____7572 = (f res.psc_range a1 b1)
in (embed_c res.psc_range uu____7572))
in FStar_Pervasives_Native.Some (uu____7571))
end
| uu____7573 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7582 -> begin
FStar_Pervasives_Native.None
end))
in (

let list_of_string' = (fun rng s -> (

let name = (fun l -> (

let uu____7602 = (

let uu____7603 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____7603))
in (mk uu____7602 rng)))
in (

let char_t = (name FStar_Parser_Const.char_lid)
in (

let charterm = (fun c -> (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))) rng))
in (

let uu____7615 = (

let uu____7618 = (FStar_String.list_of_string s)
in (FStar_List.map charterm uu____7618))
in (FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____7615))))))
in (

let string_of_list' = (fun rng l -> (

let s = (FStar_String.string_of_list l)
in (FStar_Syntax_Util.exp_string s)))
in (

let string_compare' = (fun rng s1 s2 -> (

let r = (FStar_String.compare s1 s2)
in (

let uu____7660 = (

let uu____7661 = (FStar_Util.string_of_int r)
in (FStar_BigInt.big_int_of_string uu____7661))
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng uu____7660))))
in (

let string_concat' = (fun psc args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____7683 = (arg_as_string a1)
in (match (uu____7683) with
| FStar_Pervasives_Native.Some (s1) -> begin
(

let uu____7689 = (arg_as_list FStar_Syntax_Embeddings.e_string a2)
in (match (uu____7689) with
| FStar_Pervasives_Native.Some (s2) -> begin
(

let r = (FStar_String.concat s1 s2)
in (

let uu____7702 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string psc.psc_range r)
in FStar_Pervasives_Native.Some (uu____7702)))
end
| uu____7703 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7708 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7711 -> begin
FStar_Pervasives_Native.None
end))
in (

let string_of_int1 = (fun rng i -> (

let uu____7725 = (FStar_BigInt.string_of_big_int i)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng uu____7725)))
in (

let string_of_bool1 = (fun rng b -> (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng (match (b) with
| true -> begin
"true"
end
| uu____7737 -> begin
"false"
end)))
in (

let mk_range1 = (fun psc args -> (match (args) with
| (fn)::(from_line)::(from_col)::(to_line)::(to_col)::[] -> begin
(

let uu____7762 = (

let uu____7783 = (arg_as_string fn)
in (

let uu____7786 = (arg_as_int from_line)
in (

let uu____7789 = (arg_as_int from_col)
in (

let uu____7792 = (arg_as_int to_line)
in (

let uu____7795 = (arg_as_int to_col)
in ((uu____7783), (uu____7786), (uu____7789), (uu____7792), (uu____7795)))))))
in (match (uu____7762) with
| (FStar_Pervasives_Native.Some (fn1), FStar_Pervasives_Native.Some (from_l), FStar_Pervasives_Native.Some (from_c), FStar_Pervasives_Native.Some (to_l), FStar_Pervasives_Native.Some (to_c)) -> begin
(

let r = (

let uu____7826 = (

let uu____7827 = (FStar_BigInt.to_int_fs from_l)
in (

let uu____7828 = (FStar_BigInt.to_int_fs from_c)
in (FStar_Range.mk_pos uu____7827 uu____7828)))
in (

let uu____7829 = (

let uu____7830 = (FStar_BigInt.to_int_fs to_l)
in (

let uu____7831 = (FStar_BigInt.to_int_fs to_c)
in (FStar_Range.mk_pos uu____7830 uu____7831)))
in (FStar_Range.mk_range fn1 uu____7826 uu____7829)))
in (

let uu____7832 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range psc.psc_range r)
in FStar_Pervasives_Native.Some (uu____7832)))
end
| uu____7833 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7854 -> begin
FStar_Pervasives_Native.None
end))
in (

let decidable_eq = (fun neg psc args -> (

let r = psc.psc_range
in (

let tru = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) r)
in (

let fal = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) r)
in (match (args) with
| ((_typ, uu____7887))::((a1, uu____7889))::((a2, uu____7891))::[] -> begin
(

let uu____7928 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____7928) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
fal
end
| uu____7935 -> begin
tru
end))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
tru
end
| uu____7940 -> begin
fal
end))
end
| uu____7941 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7942 -> begin
(failwith "Unexpected number of arguments")
end)))))
in (

let prims_to_fstar_range_step = (fun psc args -> (match (args) with
| ((a1, uu____7973))::[] -> begin
(

let uu____7982 = (FStar_Syntax_Embeddings.try_unembed FStar_Syntax_Embeddings.e_range a1)
in (match (uu____7982) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____7988 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range psc.psc_range r)
in FStar_Pervasives_Native.Some (uu____7988))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____7989 -> begin
(failwith "Unexpected number of arguments")
end))
in (

let basic_ops = (

let uu____8015 = (

let uu____8032 = (

let uu____8049 = (

let uu____8066 = (

let uu____8083 = (

let uu____8100 = (

let uu____8117 = (

let uu____8134 = (

let uu____8151 = (

let uu____8168 = (

let uu____8185 = (

let uu____8202 = (

let uu____8219 = (

let uu____8236 = (

let uu____8253 = (

let uu____8270 = (

let uu____8287 = (

let uu____8304 = (

let uu____8321 = (

let uu____8338 = (

let uu____8355 = (

let uu____8372 = (

let uu____8387 = (FStar_Parser_Const.p2l (("FStar")::("String")::("list_of_string")::[]))
in ((uu____8387), ((Prims.parse_int "1")), ((unary_op arg_as_string list_of_string'))))
in (

let uu____8396 = (

let uu____8413 = (

let uu____8428 = (FStar_Parser_Const.p2l (("FStar")::("String")::("string_of_list")::[]))
in ((uu____8428), ((Prims.parse_int "1")), ((unary_op (arg_as_list FStar_Syntax_Embeddings.e_char) string_of_list'))))
in (

let uu____8441 = (

let uu____8458 = (

let uu____8475 = (FStar_Parser_Const.p2l (("FStar")::("String")::("concat")::[]))
in ((uu____8475), ((Prims.parse_int "2")), (string_concat')))
in (

let uu____8486 = (

let uu____8505 = (

let uu____8522 = (FStar_Parser_Const.p2l (("Prims")::("mk_range")::[]))
in ((uu____8522), ((Prims.parse_int "5")), (mk_range1)))
in (uu____8505)::[])
in (uu____8458)::uu____8486))
in (uu____8413)::uu____8441))
in (uu____8372)::uu____8396))
in (((FStar_Parser_Const.op_notEq), ((Prims.parse_int "3")), ((decidable_eq true))))::uu____8355)
in (((FStar_Parser_Const.op_Eq), ((Prims.parse_int "3")), ((decidable_eq false))))::uu____8338)
in (((FStar_Parser_Const.string_compare), ((Prims.parse_int "2")), ((binary_op arg_as_string string_compare'))))::uu____8321)
in (((FStar_Parser_Const.string_of_bool_lid), ((Prims.parse_int "1")), ((unary_op arg_as_bool string_of_bool1))))::uu____8304)
in (((FStar_Parser_Const.string_of_int_lid), ((Prims.parse_int "1")), ((unary_op arg_as_int string_of_int1))))::uu____8287)
in (((FStar_Parser_Const.str_make_lid), ((Prims.parse_int "2")), ((mixed_binary_op arg_as_int arg_as_char (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string) (fun r x y -> (

let uu____8750 = (FStar_BigInt.to_int_fs x)
in (FStar_String.make uu____8750 y)))))))::uu____8270)
in (((FStar_Parser_Const.strcat_lid'), ((Prims.parse_int "2")), ((binary_string_op (fun x y -> (Prims.strcat x y))))))::uu____8253)
in (((FStar_Parser_Const.strcat_lid), ((Prims.parse_int "2")), ((binary_string_op (fun x y -> (Prims.strcat x y))))))::uu____8236)
in (((FStar_Parser_Const.op_Or), ((Prims.parse_int "2")), ((binary_bool_op (fun x y -> (x || y))))))::uu____8219)
in (((FStar_Parser_Const.op_And), ((Prims.parse_int "2")), ((binary_bool_op (fun x y -> (x && y))))))::uu____8202)
in (((FStar_Parser_Const.op_Negation), ((Prims.parse_int "1")), ((unary_bool_op (fun x -> (not (x)))))))::uu____8185)
in (((FStar_Parser_Const.op_Modulus), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (FStar_BigInt.mod_big_int x y))))))::uu____8168)
in (((FStar_Parser_Const.op_GTE), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (

let uu____8945 = (FStar_BigInt.ge_big_int x y)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r uu____8945)))))))::uu____8151)
in (((FStar_Parser_Const.op_GT), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (

let uu____8975 = (FStar_BigInt.gt_big_int x y)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r uu____8975)))))))::uu____8134)
in (((FStar_Parser_Const.op_LTE), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (

let uu____9005 = (FStar_BigInt.le_big_int x y)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r uu____9005)))))))::uu____8117)
in (((FStar_Parser_Const.op_LT), ((Prims.parse_int "2")), ((binary_op arg_as_int (fun r x y -> (

let uu____9035 = (FStar_BigInt.lt_big_int x y)
in (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool r uu____9035)))))))::uu____8100)
in (((FStar_Parser_Const.op_Division), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (FStar_BigInt.div_big_int x y))))))::uu____8083)
in (((FStar_Parser_Const.op_Multiply), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (FStar_BigInt.mult_big_int x y))))))::uu____8066)
in (((FStar_Parser_Const.op_Subtraction), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (FStar_BigInt.sub_big_int x y))))))::uu____8049)
in (((FStar_Parser_Const.op_Addition), ((Prims.parse_int "2")), ((binary_int_op (fun x y -> (FStar_BigInt.add_big_int x y))))))::uu____8032)
in (((FStar_Parser_Const.op_Minus), ((Prims.parse_int "1")), ((unary_int_op (fun x -> (FStar_BigInt.minus_big_int x))))))::uu____8015)
in (

let weak_ops = (

let uu____9196 = (

let uu____9217 = (FStar_Parser_Const.p2l (("FStar")::("Range")::("prims_to_fstar_range")::[]))
in ((uu____9217), ((Prims.parse_int "1")), (prims_to_fstar_range_step)))
in (uu____9196)::[])
in (

let bounded_arith_ops = (

let bounded_signed_int_types = ("Int8")::("Int16")::("Int32")::("Int64")::[]
in (

let bounded_unsigned_int_types = ("UInt8")::("UInt16")::("UInt32")::("UInt64")::("UInt128")::[]
in (

let int_as_bounded = (fun r int_to_t1 n1 -> (

let c = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r n1)
in (

let int_to_t2 = (FStar_Syntax_Syntax.fv_to_tm int_to_t1)
in (

let uu____9315 = (

let uu____9320 = (

let uu____9321 = (FStar_Syntax_Syntax.as_arg c)
in (uu____9321)::[])
in (FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____9320))
in (uu____9315 FStar_Pervasives_Native.None r)))))
in (

let add_sub_mul_v = (FStar_All.pipe_right (FStar_List.append bounded_signed_int_types bounded_unsigned_int_types) (FStar_List.collect (fun m -> (

let uu____9377 = (

let uu____9392 = (FStar_Parser_Const.p2l (("FStar")::(m)::("add")::[]))
in ((uu____9392), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____9414 uu____9415 -> (match (((uu____9414), (uu____9415))) with
| ((int_to_t1, x), (uu____9434, y)) -> begin
(

let uu____9444 = (FStar_BigInt.add_big_int x y)
in (int_as_bounded r int_to_t1 uu____9444))
end))))))
in (

let uu____9445 = (

let uu____9462 = (

let uu____9477 = (FStar_Parser_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((uu____9477), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____9499 uu____9500 -> (match (((uu____9499), (uu____9500))) with
| ((int_to_t1, x), (uu____9519, y)) -> begin
(

let uu____9529 = (FStar_BigInt.sub_big_int x y)
in (int_as_bounded r int_to_t1 uu____9529))
end))))))
in (

let uu____9530 = (

let uu____9547 = (

let uu____9562 = (FStar_Parser_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((uu____9562), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____9584 uu____9585 -> (match (((uu____9584), (uu____9585))) with
| ((int_to_t1, x), (uu____9604, y)) -> begin
(

let uu____9614 = (FStar_BigInt.mult_big_int x y)
in (int_as_bounded r int_to_t1 uu____9614))
end))))))
in (

let uu____9615 = (

let uu____9632 = (

let uu____9647 = (FStar_Parser_Const.p2l (("FStar")::(m)::("v")::[]))
in ((uu____9647), ((Prims.parse_int "1")), ((unary_op arg_as_bounded_int (fun r uu____9665 -> (match (uu____9665) with
| (int_to_t1, x) -> begin
(FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int r x)
end))))))
in (uu____9632)::[])
in (uu____9547)::uu____9615))
in (uu____9462)::uu____9530))
in (uu____9377)::uu____9445)))))
in (

let div_mod_unsigned = (FStar_All.pipe_right bounded_unsigned_int_types (FStar_List.collect (fun m -> (

let uu____9795 = (

let uu____9810 = (FStar_Parser_Const.p2l (("FStar")::(m)::("div")::[]))
in ((uu____9810), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____9832 uu____9833 -> (match (((uu____9832), (uu____9833))) with
| ((int_to_t1, x), (uu____9852, y)) -> begin
(

let uu____9862 = (FStar_BigInt.div_big_int x y)
in (int_as_bounded r int_to_t1 uu____9862))
end))))))
in (

let uu____9863 = (

let uu____9880 = (

let uu____9895 = (FStar_Parser_Const.p2l (("FStar")::(m)::("rem")::[]))
in ((uu____9895), ((Prims.parse_int "2")), ((binary_op arg_as_bounded_int (fun r uu____9917 uu____9918 -> (match (((uu____9917), (uu____9918))) with
| ((int_to_t1, x), (uu____9937, y)) -> begin
(

let uu____9947 = (FStar_BigInt.mod_big_int x y)
in (int_as_bounded r int_to_t1 uu____9947))
end))))))
in (uu____9880)::[])
in (uu____9795)::uu____9863)))))
in (FStar_List.append add_sub_mul_v div_mod_unsigned))))))
in (

let strong_steps = (FStar_List.map (as_primitive_step true) (FStar_List.append basic_ops bounded_arith_ops))
in (

let weak_steps = (FStar_List.map (as_primitive_step false) weak_ops)
in (FStar_All.pipe_left prim_from_list (FStar_List.append strong_steps weak_steps)))))))))))))))))))))))))))))))))


let equality_ops : primitive_step FStar_Util.psmap = (

let interp_prop = (fun psc args -> (

let r = psc.psc_range
in (match (args) with
| ((_typ, uu____10077))::((a1, uu____10079))::((a2, uu____10081))::[] -> begin
(

let uu____10118 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____10118) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___144_10124 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___144_10124.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___144_10124.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___145_10128 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___145_10128.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___145_10128.FStar_Syntax_Syntax.vars}))
end
| uu____10129 -> begin
FStar_Pervasives_Native.None
end))
end
| ((_typ, uu____10131))::(uu____10132)::((a1, uu____10134))::((a2, uu____10136))::[] -> begin
(

let uu____10185 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____10185) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___144_10191 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___144_10191.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___144_10191.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___145_10195 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___145_10195.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___145_10195.FStar_Syntax_Syntax.vars}))
end
| uu____10196 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____10197 -> begin
(failwith "Unexpected number of arguments")
end)))
in (

let propositional_equality = {name = FStar_Parser_Const.eq2_lid; arity = (Prims.parse_int "3"); auto_reflect = FStar_Pervasives_Native.None; strong_reduction_ok = true; requires_binder_substitution = false; interpretation = interp_prop}
in (

let hetero_propositional_equality = {name = FStar_Parser_Const.eq3_lid; arity = (Prims.parse_int "4"); auto_reflect = FStar_Pervasives_Native.None; strong_reduction_ok = true; requires_binder_substitution = false; interpretation = interp_prop}
in (prim_from_list ((propositional_equality)::(hetero_propositional_equality)::[])))))


let unembed_binder_knot : FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let unembed_binder : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option = (fun t -> (

let uu____10299 = (FStar_ST.op_Bang unembed_binder_knot)
in (match (uu____10299) with
| FStar_Pervasives_Native.Some (e) -> begin
(FStar_Syntax_Embeddings.unembed e t)
end
| FStar_Pervasives_Native.None -> begin
((FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_UnembedBinderKnot), ("unembed_binder_knot is unset!")));
FStar_Pervasives_Native.None;
)
end)))


let mk_psc_subst : 'Auu____10357 . cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____10357) FStar_Pervasives_Native.option * closure) Prims.list  ->  FStar_Syntax_Syntax.subst_elt Prims.list = (fun cfg env -> (FStar_List.fold_right (fun uu____10419 subst1 -> (match (uu____10419) with
| (binder_opt, closure) -> begin
(match (((binder_opt), (closure))) with
| (FStar_Pervasives_Native.Some (b), Clos (env1, term, uu____10460, uu____10461)) -> begin
(

let uu____10520 = b
in (match (uu____10520) with
| (bv, uu____10528) -> begin
(

let uu____10529 = (

let uu____10530 = (FStar_Syntax_Util.is_constructed_typ bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.binder_lid)
in (not (uu____10530)))
in (match (uu____10529) with
| true -> begin
subst1
end
| uu____10533 -> begin
(

let term1 = (closure_as_term cfg env1 term)
in (

let uu____10535 = (unembed_binder term1)
in (match (uu____10535) with
| FStar_Pervasives_Native.None -> begin
subst1
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let b1 = (

let uu____10542 = (

let uu___146_10543 = bv
in (

let uu____10544 = (FStar_Syntax_Subst.subst subst1 (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___146_10543.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___146_10543.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____10544}))
in (FStar_Syntax_Syntax.freshen_bv uu____10542))
in (

let b_for_x = (

let uu____10548 = (

let uu____10555 = (FStar_Syntax_Syntax.bv_to_name b1)
in (((FStar_Pervasives_Native.fst x)), (uu____10555)))
in FStar_Syntax_Syntax.NT (uu____10548))
in (

let subst2 = (FStar_List.filter (fun uu___88_10565 -> (match (uu___88_10565) with
| FStar_Syntax_Syntax.NT (uu____10566, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (b'); FStar_Syntax_Syntax.pos = uu____10568; FStar_Syntax_Syntax.vars = uu____10569}) -> begin
(

let uu____10574 = (FStar_Ident.ident_equals b1.FStar_Syntax_Syntax.ppname b'.FStar_Syntax_Syntax.ppname)
in (not (uu____10574)))
end
| uu____10575 -> begin
true
end)) subst1)
in (b_for_x)::subst2)))
end)))
end))
end))
end
| uu____10576 -> begin
subst1
end)
end)) env []))


let reduce_primops : 'Auu____10599 'Auu____10600 . cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____10599) FStar_Pervasives_Native.option * closure) Prims.list  ->  'Auu____10600  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack tm -> (match ((not (cfg.steps.primops))) with
| true -> begin
tm
end
| uu____10645 -> begin
(

let uu____10646 = (FStar_Syntax_Util.head_and_args tm)
in (match (uu____10646) with
| (head1, args) -> begin
(

let uu____10683 = (

let uu____10684 = (FStar_Syntax_Util.un_uinst head1)
in uu____10684.FStar_Syntax_Syntax.n)
in (match (uu____10683) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____10688 = (find_prim_step cfg fv)
in (match (uu____10688) with
| FStar_Pervasives_Native.Some (prim_step) when (prim_step.strong_reduction_ok || (not (cfg.strong))) -> begin
(

let l = (FStar_List.length args)
in (match ((l < prim_step.arity)) with
| true -> begin
((log_primops cfg (fun uu____10710 -> (

let uu____10711 = (FStar_Syntax_Print.lid_to_string prim_step.name)
in (

let uu____10712 = (FStar_Util.string_of_int l)
in (

let uu____10719 = (FStar_Util.string_of_int prim_step.arity)
in (FStar_Util.print3 "primop: found partially applied %s (%s/%s args)\n" uu____10711 uu____10712 uu____10719))))));
tm;
)
end
| uu____10720 -> begin
(

let uu____10721 = (match ((Prims.op_Equality l prim_step.arity)) with
| true -> begin
((args), ([]))
end
| uu____10788 -> begin
(FStar_List.splitAt prim_step.arity args)
end)
in (match (uu____10721) with
| (args_1, args_2) -> begin
((log_primops cfg (fun uu____10832 -> (

let uu____10833 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: trying to reduce <%s>\n" uu____10833))));
(

let psc = {psc_range = head1.FStar_Syntax_Syntax.pos; psc_subst = (fun uu____10836 -> (match (prim_step.requires_binder_substitution) with
| true -> begin
(mk_psc_subst cfg env)
end
| uu____10837 -> begin
[]
end))}
in (

let uu____10838 = (prim_step.interpretation psc args_1)
in (match (uu____10838) with
| FStar_Pervasives_Native.None -> begin
((log_primops cfg (fun uu____10844 -> (

let uu____10845 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: <%s> did not reduce\n" uu____10845))));
tm;
)
end
| FStar_Pervasives_Native.Some (reduced) -> begin
((log_primops cfg (fun uu____10851 -> (

let uu____10852 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____10853 = (FStar_Syntax_Print.term_to_string reduced)
in (FStar_Util.print2 "primop: <%s> reduced to <%s>\n" uu____10852 uu____10853)))));
(FStar_Syntax_Util.mk_app reduced args_2);
)
end)));
)
end))
end))
end
| FStar_Pervasives_Native.Some (uu____10854) -> begin
((log_primops cfg (fun uu____10858 -> (

let uu____10859 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: not reducing <%s> since we\'re doing strong reduction\n" uu____10859))));
tm;
)
end
| FStar_Pervasives_Native.None -> begin
tm
end))
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of) when (not (cfg.strong)) -> begin
((log_primops cfg (fun uu____10863 -> (

let uu____10864 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: reducing <%s>\n" uu____10864))));
(match (args) with
| ((a1, uu____10866))::[] -> begin
(FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range tm.FStar_Syntax_Syntax.pos a1.FStar_Syntax_Syntax.pos)
end
| uu____10883 -> begin
tm
end);
)
end
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of) when (not (cfg.strong)) -> begin
((log_primops cfg (fun uu____10895 -> (

let uu____10896 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "primop: reducing <%s>\n" uu____10896))));
(match (args) with
| ((t, uu____10898))::((r, uu____10900))::[] -> begin
(

let uu____10927 = (FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_range r)
in (match (uu____10927) with
| FStar_Pervasives_Native.Some (rng) -> begin
(

let uu___147_10931 = t
in {FStar_Syntax_Syntax.n = uu___147_10931.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = rng; FStar_Syntax_Syntax.vars = uu___147_10931.FStar_Syntax_Syntax.vars})
end
| FStar_Pervasives_Native.None -> begin
tm
end))
end
| uu____10934 -> begin
tm
end);
)
end
| uu____10943 -> begin
tm
end))
end))
end))


let reduce_equality : 'Auu____10954 'Auu____10955 . cfg  ->  ((FStar_Syntax_Syntax.bv * 'Auu____10954) FStar_Pervasives_Native.option * closure) Prims.list  ->  'Auu____10955  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg tm -> (reduce_primops (

let uu___148_10999 = cfg
in {steps = (

let uu___149_11002 = default_steps
in {beta = uu___149_11002.beta; iota = uu___149_11002.iota; zeta = uu___149_11002.zeta; weak = uu___149_11002.weak; hnf = uu___149_11002.hnf; primops = true; do_not_unfold_pure_lets = uu___149_11002.do_not_unfold_pure_lets; unfold_until = uu___149_11002.unfold_until; unfold_only = uu___149_11002.unfold_only; unfold_fully = uu___149_11002.unfold_fully; unfold_attr = uu___149_11002.unfold_attr; unfold_tac = uu___149_11002.unfold_tac; pure_subterms_within_computations = uu___149_11002.pure_subterms_within_computations; simplify = uu___149_11002.simplify; erase_universes = uu___149_11002.erase_universes; allow_unbound_universes = uu___149_11002.allow_unbound_universes; reify_ = uu___149_11002.reify_; compress_uvars = uu___149_11002.compress_uvars; no_full_norm = uu___149_11002.no_full_norm; check_no_uvars = uu___149_11002.check_no_uvars; unmeta = uu___149_11002.unmeta; unascribe = uu___149_11002.unascribe; in_full_norm_request = uu___149_11002.in_full_norm_request; weakly_reduce_scrutinee = uu___149_11002.weakly_reduce_scrutinee}); tcenv = uu___148_10999.tcenv; debug = uu___148_10999.debug; delta_level = uu___148_10999.delta_level; primitive_steps = equality_ops; strong = uu___148_10999.strong; memoize_lazy = uu___148_10999.memoize_lazy; normalize_pure_lets = uu___148_10999.normalize_pure_lets}) tm))


let is_norm_request : 'Auu____11009 . FStar_Syntax_Syntax.term  ->  'Auu____11009 Prims.list  ->  Prims.bool = (fun hd1 args -> (

let uu____11024 = (

let uu____11031 = (

let uu____11032 = (FStar_Syntax_Util.un_uinst hd1)
in uu____11032.FStar_Syntax_Syntax.n)
in ((uu____11031), (args)))
in (match (uu____11024) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____11038)::(uu____11039)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____11043)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (steps)::(uu____11048)::(uu____11049)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm)
end
| uu____11052 -> begin
false
end)))


let tr_norm_step : FStar_Syntax_Embeddings.norm_step  ->  step Prims.list = (fun uu___89_11065 -> (match (uu___89_11065) with
| FStar_Syntax_Embeddings.Zeta -> begin
(Zeta)::[]
end
| FStar_Syntax_Embeddings.Iota -> begin
(Iota)::[]
end
| FStar_Syntax_Embeddings.Delta -> begin
(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]
end
| FStar_Syntax_Embeddings.Simpl -> begin
(Simplify)::[]
end
| FStar_Syntax_Embeddings.Weak -> begin
(Weak)::[]
end
| FStar_Syntax_Embeddings.HNF -> begin
(HNF)::[]
end
| FStar_Syntax_Embeddings.Primops -> begin
(Primops)::[]
end
| FStar_Syntax_Embeddings.UnfoldOnly (names1) -> begin
(

let uu____11071 = (

let uu____11074 = (

let uu____11075 = (FStar_List.map FStar_Ident.lid_of_str names1)
in UnfoldOnly (uu____11075))
in (uu____11074)::[])
in (UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::uu____11071)
end
| FStar_Syntax_Embeddings.UnfoldFully (names1) -> begin
(

let uu____11081 = (

let uu____11084 = (

let uu____11085 = (FStar_List.map FStar_Ident.lid_of_str names1)
in UnfoldFully (uu____11085))
in (uu____11084)::[])
in (UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::uu____11081)
end
| FStar_Syntax_Embeddings.UnfoldAttr (t) -> begin
(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(UnfoldAttr (t))::[]
end))


let tr_norm_steps : FStar_Syntax_Embeddings.norm_step Prims.list  ->  step Prims.list = (fun s -> (FStar_List.concatMap tr_norm_step s))


let get_norm_request : 'Auu____11106 . (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term * 'Auu____11106) Prims.list  ->  (step Prims.list * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun full_norm args -> (

let parse_steps = (fun s -> (

let uu____11152 = (

let uu____11157 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_norm_step)
in (FStar_Syntax_Embeddings.try_unembed uu____11157 s))
in (match (uu____11152) with
| FStar_Pervasives_Native.Some (steps) -> begin
(

let uu____11173 = (tr_norm_steps steps)
in FStar_Pervasives_Native.Some (uu____11173))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))
in (match (args) with
| (uu____11190)::((tm, uu____11192))::[] -> begin
(

let s = (Beta)::(Zeta)::(Iota)::(Primops)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Reify)::[]
in FStar_Pervasives_Native.Some (((s), (tm))))
end
| ((tm, uu____11221))::[] -> begin
(

let s = (Beta)::(Zeta)::(Iota)::(Primops)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Reify)::[]
in FStar_Pervasives_Native.Some (((s), (tm))))
end
| ((steps, uu____11242))::(uu____11243)::((tm, uu____11245))::[] -> begin
(

let add_exclude = (fun s z -> (match ((FStar_List.contains z s)) with
| true -> begin
s
end
| uu____11285 -> begin
(Exclude (z))::s
end))
in (

let uu____11286 = (

let uu____11291 = (full_norm steps)
in (parse_steps uu____11291))
in (match (uu____11286) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (s) -> begin
(

let s1 = (Beta)::s
in (

let s2 = (add_exclude s1 Zeta)
in (

let s3 = (add_exclude s2 Iota)
in FStar_Pervasives_Native.Some (((s3), (tm))))))
end)))
end
| uu____11330 -> begin
FStar_Pervasives_Native.None
end)))


let is_reify_head : stack_elt Prims.list  ->  Prims.bool = (fun uu___90_11349 -> (match (uu___90_11349) with
| (App (uu____11352, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____11353; FStar_Syntax_Syntax.vars = uu____11354}, uu____11355, uu____11356))::uu____11357 -> begin
true
end
| uu____11364 -> begin
false
end))


let firstn : 'Auu____11373 . Prims.int  ->  'Auu____11373 Prims.list  ->  ('Auu____11373 Prims.list * 'Auu____11373 Prims.list) = (fun k l -> (match (((FStar_List.length l) < k)) with
| true -> begin
((l), ([]))
end
| uu____11400 -> begin
(FStar_Util.first_N k l)
end))


let should_reify : cfg  ->  stack_elt Prims.list  ->  Prims.bool = (fun cfg stack -> (match (stack) with
| (App (uu____11415, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____11416; FStar_Syntax_Syntax.vars = uu____11417}, uu____11418, uu____11419))::uu____11420 -> begin
cfg.steps.reify_
end
| uu____11427 -> begin
false
end))


let rec maybe_weakly_reduced : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun tm -> (

let aux_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.GTotal (t, uu____11450) -> begin
(maybe_weakly_reduced t)
end
| FStar_Syntax_Syntax.Total (t, uu____11460) -> begin
(maybe_weakly_reduced t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
((maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) || (FStar_Util.for_some (fun uu____11479 -> (match (uu____11479) with
| (a, uu____11487) -> begin
(maybe_weakly_reduced a)
end)) ct.FStar_Syntax_Syntax.effect_args))
end))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____11493) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (uu____11518) -> begin
false
end
| FStar_Syntax_Syntax.Tm_uvar (uu____11519) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____11536) -> begin
false
end
| FStar_Syntax_Syntax.Tm_bvar (uu____11537) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (uu____11538) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (uu____11539) -> begin
false
end
| FStar_Syntax_Syntax.Tm_lazy (uu____11540) -> begin
false
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| FStar_Syntax_Syntax.Tm_uinst (uu____11541) -> begin
false
end
| FStar_Syntax_Syntax.Tm_quoted (uu____11548) -> begin
false
end
| FStar_Syntax_Syntax.Tm_let (uu____11555) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____11568) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____11585) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____11598) -> begin
true
end
| FStar_Syntax_Syntax.Tm_match (uu____11605) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (t1, args) -> begin
((maybe_weakly_reduced t1) || (FStar_All.pipe_right args (FStar_Util.for_some (fun uu____11667 -> (match (uu____11667) with
| (a, uu____11675) -> begin
(maybe_weakly_reduced a)
end)))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____11682) -> begin
(((maybe_weakly_reduced t1) || (match ((FStar_Pervasives_Native.fst asc)) with
| FStar_Util.Inl (t2) -> begin
(maybe_weakly_reduced t2)
end
| FStar_Util.Inr (c2) -> begin
(aux_comp c2)
end)) || (match ((FStar_Pervasives_Native.snd asc)) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (tac) -> begin
(maybe_weakly_reduced tac)
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, m) -> begin
((maybe_weakly_reduced t1) || (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(FStar_Util.for_some (FStar_Util.for_some (fun uu____11804 -> (match (uu____11804) with
| (a, uu____11812) -> begin
(maybe_weakly_reduced a)
end))) args)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (uu____11817, uu____11818, t') -> begin
(maybe_weakly_reduced t')
end
| FStar_Syntax_Syntax.Meta_monadic (uu____11824, t') -> begin
(maybe_weakly_reduced t')
end
| FStar_Syntax_Syntax.Meta_labeled (uu____11830) -> begin
false
end
| FStar_Syntax_Syntax.Meta_desugared (uu____11837) -> begin
false
end
| FStar_Syntax_Syntax.Meta_named (uu____11838) -> begin
false
end))
end))))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t1 = ((match (cfg.debug.norm_delayed) with
| true -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____12130) -> begin
(

let uu____12155 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "NORM delayed: %s\n" uu____12155))
end
| uu____12156 -> begin
()
end)
end
| uu____12157 -> begin
()
end);
(FStar_Syntax_Subst.compress t);
)
in ((log cfg (fun uu____12164 -> (

let uu____12165 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____12166 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12167 = (FStar_Util.string_of_int (FStar_List.length env))
in (

let uu____12174 = (

let uu____12175 = (

let uu____12178 = (firstn (Prims.parse_int "4") stack)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____12178))
in (stack_to_string uu____12175))
in (FStar_Util.print4 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n" uu____12165 uu____12166 uu____12167 uu____12174)))))));
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_constant (uu____12201) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_name (uu____12202) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_lazy (uu____12203) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____12204; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = uu____12205}) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____12208; FStar_Syntax_Syntax.fv_delta = uu____12209; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____12210; FStar_Syntax_Syntax.fv_delta = uu____12211; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____12212))}) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_quoted (uu____12219) -> begin
(

let uu____12226 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____12226))
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) when (((not (cfg.steps.no_full_norm)) && (is_norm_request hd1 args)) && (

let uu____12256 = (FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid)
in (not (uu____12256)))) -> begin
(

let cfg' = (

let uu___150_12258 = cfg
in {steps = (

let uu___151_12261 = cfg.steps
in {beta = uu___151_12261.beta; iota = uu___151_12261.iota; zeta = uu___151_12261.zeta; weak = uu___151_12261.weak; hnf = uu___151_12261.hnf; primops = uu___151_12261.primops; do_not_unfold_pure_lets = false; unfold_until = uu___151_12261.unfold_until; unfold_only = FStar_Pervasives_Native.None; unfold_fully = FStar_Pervasives_Native.None; unfold_attr = uu___151_12261.unfold_attr; unfold_tac = uu___151_12261.unfold_tac; pure_subterms_within_computations = uu___151_12261.pure_subterms_within_computations; simplify = uu___151_12261.simplify; erase_universes = uu___151_12261.erase_universes; allow_unbound_universes = uu___151_12261.allow_unbound_universes; reify_ = uu___151_12261.reify_; compress_uvars = uu___151_12261.compress_uvars; no_full_norm = uu___151_12261.no_full_norm; check_no_uvars = uu___151_12261.check_no_uvars; unmeta = uu___151_12261.unmeta; unascribe = uu___151_12261.unascribe; in_full_norm_request = uu___151_12261.in_full_norm_request; weakly_reduce_scrutinee = uu___151_12261.weakly_reduce_scrutinee}); tcenv = uu___150_12258.tcenv; debug = uu___150_12258.debug; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]; primitive_steps = uu___150_12258.primitive_steps; strong = uu___150_12258.strong; memoize_lazy = uu___150_12258.memoize_lazy; normalize_pure_lets = true})
in (

let uu____12266 = (get_norm_request (norm cfg' env []) args)
in (match (uu____12266) with
| FStar_Pervasives_Native.None -> begin
(

let stack1 = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____12297 stack1 -> (match (uu____12297) with
| (a, aq) -> begin
(

let uu____12309 = (

let uu____12310 = (

let uu____12317 = (

let uu____12318 = (

let uu____12349 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____12349), (false)))
in Clos (uu____12318))
in ((uu____12317), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____12310))
in (uu____12309)::stack1)
end)) args))
in ((log cfg (fun uu____12481 -> (

let uu____12482 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____12482))));
(norm cfg env stack1 hd1);
))
end
| FStar_Pervasives_Native.Some (s, tm) -> begin
(

let delta_level = (

let uu____12504 = (FStar_All.pipe_right s (FStar_Util.for_some (fun uu___91_12509 -> (match (uu___91_12509) with
| UnfoldUntil (uu____12510) -> begin
true
end
| UnfoldOnly (uu____12511) -> begin
true
end
| UnfoldFully (uu____12514) -> begin
true
end
| uu____12517 -> begin
false
end))))
in (match (uu____12504) with
| true -> begin
(FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]
end
| uu____12520 -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end))
in (

let cfg'1 = (

let uu___152_12522 = cfg
in (

let uu____12523 = (

let uu___153_12524 = (to_fsteps s)
in {beta = uu___153_12524.beta; iota = uu___153_12524.iota; zeta = uu___153_12524.zeta; weak = uu___153_12524.weak; hnf = uu___153_12524.hnf; primops = uu___153_12524.primops; do_not_unfold_pure_lets = uu___153_12524.do_not_unfold_pure_lets; unfold_until = uu___153_12524.unfold_until; unfold_only = uu___153_12524.unfold_only; unfold_fully = uu___153_12524.unfold_fully; unfold_attr = uu___153_12524.unfold_attr; unfold_tac = uu___153_12524.unfold_tac; pure_subterms_within_computations = uu___153_12524.pure_subterms_within_computations; simplify = uu___153_12524.simplify; erase_universes = uu___153_12524.erase_universes; allow_unbound_universes = uu___153_12524.allow_unbound_universes; reify_ = uu___153_12524.reify_; compress_uvars = uu___153_12524.compress_uvars; no_full_norm = uu___153_12524.no_full_norm; check_no_uvars = uu___153_12524.check_no_uvars; unmeta = uu___153_12524.unmeta; unascribe = uu___153_12524.unascribe; in_full_norm_request = true; weakly_reduce_scrutinee = uu___153_12524.weakly_reduce_scrutinee})
in {steps = uu____12523; tcenv = uu___152_12522.tcenv; debug = uu___152_12522.debug; delta_level = delta_level; primitive_steps = uu___152_12522.primitive_steps; strong = uu___152_12522.strong; memoize_lazy = uu___152_12522.memoize_lazy; normalize_pure_lets = true}))
in (

let stack' = (

let tail1 = (Cfg (cfg))::stack
in (match (cfg.debug.print_normalized) with
| true -> begin
(

let uu____12533 = (

let uu____12534 = (

let uu____12539 = (FStar_Util.now ())
in ((t1), (uu____12539)))
in Debug (uu____12534))
in (uu____12533)::tail1)
end
| uu____12540 -> begin
tail1
end))
in (norm cfg'1 env stack' tm))))
end)))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u1 = (norm_universe cfg env u)
in (

let uu____12543 = (mk (FStar_Syntax_Syntax.Tm_type (u1)) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack uu____12543)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(match (cfg.steps.erase_universes) with
| true -> begin
(norm cfg env stack t')
end
| uu____12550 -> begin
(

let us1 = (

let uu____12552 = (

let uu____12559 = (FStar_List.map (norm_universe cfg env) us)
in ((uu____12559), (t1.FStar_Syntax_Syntax.pos)))
in UnivArgs (uu____12552))
in (

let stack1 = (us1)::stack
in (norm cfg env stack1 t')))
end)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let qninfo = (

let uu____12569 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_TypeChecker_Env.lookup_qname cfg.tcenv uu____12569))
in (

let uu____12570 = (FStar_TypeChecker_Env.qninfo_is_action qninfo)
in (match (uu____12570) with
| true -> begin
(

let b = (should_reify cfg stack)
in ((log cfg (fun uu____12576 -> (

let uu____12577 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12578 = (FStar_Util.string_of_bool b)
in (FStar_Util.print2 ">>> For DM4F action %s, should_reify = %s\n" uu____12577 uu____12578)))));
(match (b) with
| true -> begin
(

let uu____12579 = (FStar_List.tl stack)
in (do_unfold_fv cfg env uu____12579 t1 qninfo fv))
end
| uu____12582 -> begin
(rebuild cfg env stack t1)
end);
))
end
| uu____12583 -> begin
(

let should_delta = (((

let uu____12587 = (find_prim_step cfg fv)
in (FStar_Option.isNone uu____12587)) && (match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let ((is_rec, uu____12600), uu____12601); FStar_Syntax_Syntax.sigrng = uu____12602; FStar_Syntax_Syntax.sigquals = qs; FStar_Syntax_Syntax.sigmeta = uu____12604; FStar_Syntax_Syntax.sigattrs = uu____12605}, uu____12606), uu____12607) -> begin
((not ((FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect qs))) && ((not (is_rec)) || cfg.steps.zeta))
end
| uu____12672 -> begin
true
end)) && (FStar_All.pipe_right cfg.delta_level (FStar_Util.for_some (fun uu___92_12676 -> (match (uu___92_12676) with
| FStar_TypeChecker_Env.UnfoldTac -> begin
false
end
| FStar_TypeChecker_Env.NoDelta -> begin
false
end
| FStar_TypeChecker_Env.Inlining -> begin
true
end
| FStar_TypeChecker_Env.Eager_unfolding_only -> begin
true
end
| FStar_TypeChecker_Env.Unfold (l) -> begin
(FStar_TypeChecker_Common.delta_depth_greater_than fv.FStar_Syntax_Syntax.fv_delta l)
end)))))
in (

let should_delta1 = (should_delta && (

let attrs = (FStar_TypeChecker_Env.attrs_of_qninfo qninfo)
in (((not (cfg.steps.unfold_tac)) || (

let uu____12686 = (cases (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.tac_opaque_attr)) false attrs)
in (not (uu____12686)))) && ((match (cfg.steps.unfold_only) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (lids) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
end) || (match (((attrs), (cfg.steps.unfold_attr))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (uu____12705)) -> begin
false
end
| (FStar_Pervasives_Native.Some (ats), FStar_Pervasives_Native.Some (ats')) -> begin
(FStar_Util.for_some (fun at -> (FStar_Util.for_some (FStar_Syntax_Util.attr_eq at) ats')) ats)
end
| (uu____12740, uu____12741) -> begin
false
end)))))
in (

let uu____12758 = (match (cfg.steps.unfold_fully) with
| FStar_Pervasives_Native.None -> begin
((should_delta1), (false))
end
| FStar_Pervasives_Native.Some (lids) -> begin
(

let uu____12774 = (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) lids)
in (match (uu____12774) with
| true -> begin
((true), (true))
end
| uu____12779 -> begin
((false), (false))
end))
end)
in (match (uu____12758) with
| (should_delta2, fully) -> begin
((log cfg (fun uu____12787 -> (

let uu____12788 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____12789 = (FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos)
in (

let uu____12790 = (FStar_Util.string_of_bool should_delta2)
in (FStar_Util.print3 ">>> For %s (%s), should_delta = %s\n" uu____12788 uu____12789 uu____12790))))));
(match (should_delta2) with
| true -> begin
(

let uu____12791 = (match (fully) with
| true -> begin
(((Cfg (cfg))::stack), ((

let uu___154_12807 = cfg
in {steps = (

let uu___155_12810 = cfg.steps
in {beta = uu___155_12810.beta; iota = false; zeta = false; weak = false; hnf = false; primops = false; do_not_unfold_pure_lets = uu___155_12810.do_not_unfold_pure_lets; unfold_until = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant); unfold_only = FStar_Pervasives_Native.None; unfold_fully = FStar_Pervasives_Native.None; unfold_attr = uu___155_12810.unfold_attr; unfold_tac = uu___155_12810.unfold_tac; pure_subterms_within_computations = uu___155_12810.pure_subterms_within_computations; simplify = false; erase_universes = uu___155_12810.erase_universes; allow_unbound_universes = uu___155_12810.allow_unbound_universes; reify_ = uu___155_12810.reify_; compress_uvars = uu___155_12810.compress_uvars; no_full_norm = uu___155_12810.no_full_norm; check_no_uvars = uu___155_12810.check_no_uvars; unmeta = uu___155_12810.unmeta; unascribe = uu___155_12810.unascribe; in_full_norm_request = uu___155_12810.in_full_norm_request; weakly_reduce_scrutinee = uu___155_12810.weakly_reduce_scrutinee}); tcenv = uu___154_12807.tcenv; debug = uu___154_12807.debug; delta_level = uu___154_12807.delta_level; primitive_steps = uu___154_12807.primitive_steps; strong = uu___154_12807.strong; memoize_lazy = uu___154_12807.memoize_lazy; normalize_pure_lets = uu___154_12807.normalize_pure_lets})))
end
| uu____12815 -> begin
((stack), (cfg))
end)
in (match (uu____12791) with
| (stack1, cfg1) -> begin
(do_unfold_fv cfg1 env stack1 t1 qninfo fv)
end))
end
| uu____12822 -> begin
(rebuild cfg env stack t1)
end);
)
end))))
end)))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____12824 = (lookup_bvar env x)
in (match (uu____12824) with
| Univ (uu____12825) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(failwith "Term variable not found")
end
| Clos (env1, t0, r, fix) -> begin
(match (((not (fix)) || cfg.steps.zeta)) with
| true -> begin
(

let uu____12874 = (FStar_ST.op_Bang r)
in (match (uu____12874) with
| FStar_Pervasives_Native.Some (env2, t') -> begin
((log cfg (fun uu____13050 -> (

let uu____13051 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____13052 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" uu____13051 uu____13052)))));
(

let uu____13053 = (maybe_weakly_reduced t')
in (match (uu____13053) with
| true -> begin
(match (stack) with
| [] when (cfg.steps.weak || cfg.steps.compress_uvars) -> begin
(rebuild cfg env2 stack t')
end
| uu____13054 -> begin
(norm cfg env2 stack t')
end)
end
| uu____13055 -> begin
(rebuild cfg env2 stack t')
end));
)
end
| FStar_Pervasives_Native.None -> begin
(norm cfg env1 ((MemoLazy (r))::stack) t0)
end))
end
| uu____13173 -> begin
(norm cfg env1 stack t0)
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack) with
| (UnivArgs (uu____13197))::uu____13198 -> begin
(failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (uu____13207))::uu____13208 -> begin
(failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, uu____13220, uu____13221))::stack_rest -> begin
(match (c) with
| Univ (uu____13225) -> begin
(norm cfg ((((FStar_Pervasives_Native.None), (c)))::env) stack_rest t1)
end
| uu____13234 -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (b)::[] -> begin
((log cfg (fun uu____13255 -> (

let uu____13256 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____13256))));
(norm cfg ((((FStar_Pervasives_Native.Some (b)), (c)))::env) stack_rest body);
)
end
| (b)::tl1 -> begin
((log cfg (fun uu____13296 -> (

let uu____13297 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" uu____13297))));
(

let body1 = (mk (FStar_Syntax_Syntax.Tm_abs (((tl1), (body), (lopt)))) t1.FStar_Syntax_Syntax.pos)
in (norm cfg ((((FStar_Pervasives_Native.Some (b)), (c)))::env) stack_rest body1));
)
end)
end)
end
| (Cfg (cfg1))::stack1 -> begin
(norm cfg1 env stack1 t1)
end
| (MemoLazy (r))::stack1 -> begin
((set_memo cfg r ((env), (t1)));
(log cfg (fun uu____13423 -> (

let uu____13424 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "\tSet memo %s\n" uu____13424))));
(norm cfg env stack1 t1);
)
end
| (Debug (uu____13425))::uu____13426 -> begin
(match (cfg.steps.weak) with
| true -> begin
(

let t2 = (match (cfg.steps.in_full_norm_request) with
| true -> begin
(closure_as_term cfg env t1)
end
| uu____13434 -> begin
(

let steps' = (

let uu___156_13436 = cfg.steps
in {beta = uu___156_13436.beta; iota = false; zeta = false; weak = false; hnf = uu___156_13436.hnf; primops = false; do_not_unfold_pure_lets = true; unfold_until = uu___156_13436.unfold_until; unfold_only = uu___156_13436.unfold_only; unfold_fully = uu___156_13436.unfold_fully; unfold_attr = uu___156_13436.unfold_attr; unfold_tac = uu___156_13436.unfold_tac; pure_subterms_within_computations = false; simplify = false; erase_universes = uu___156_13436.erase_universes; allow_unbound_universes = uu___156_13436.allow_unbound_universes; reify_ = false; compress_uvars = uu___156_13436.compress_uvars; no_full_norm = true; check_no_uvars = uu___156_13436.check_no_uvars; unmeta = false; unascribe = false; in_full_norm_request = uu___156_13436.in_full_norm_request; weakly_reduce_scrutinee = uu___156_13436.weakly_reduce_scrutinee})
in (

let cfg' = (

let uu___157_13438 = cfg
in {steps = steps'; tcenv = uu___157_13438.tcenv; debug = uu___157_13438.debug; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]; primitive_steps = uu___157_13438.primitive_steps; strong = uu___157_13438.strong; memoize_lazy = uu___157_13438.memoize_lazy; normalize_pure_lets = uu___157_13438.normalize_pure_lets})
in (norm cfg' env [] t1)))
end)
in (rebuild cfg env stack t2))
end
| uu____13439 -> begin
(

let uu____13440 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____13440) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____13482 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.steps.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____13519 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____13519))))
end
| uu____13520 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___158_13524 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___158_13524.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___158_13524.FStar_Syntax_Syntax.residual_flags})))
end
| uu____13525 -> begin
lopt
end)
in ((log cfg (fun uu____13531 -> (

let uu____13532 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____13532))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___159_13541 = cfg
in {steps = uu___159_13541.steps; tcenv = uu___159_13541.tcenv; debug = uu___159_13541.debug; delta_level = uu___159_13541.delta_level; primitive_steps = uu___159_13541.primitive_steps; strong = true; memoize_lazy = uu___159_13541.memoize_lazy; normalize_pure_lets = uu___159_13541.normalize_pure_lets})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Meta (uu____13552))::uu____13553 -> begin
(match (cfg.steps.weak) with
| true -> begin
(

let t2 = (match (cfg.steps.in_full_norm_request) with
| true -> begin
(closure_as_term cfg env t1)
end
| uu____13563 -> begin
(

let steps' = (

let uu___156_13565 = cfg.steps
in {beta = uu___156_13565.beta; iota = false; zeta = false; weak = false; hnf = uu___156_13565.hnf; primops = false; do_not_unfold_pure_lets = true; unfold_until = uu___156_13565.unfold_until; unfold_only = uu___156_13565.unfold_only; unfold_fully = uu___156_13565.unfold_fully; unfold_attr = uu___156_13565.unfold_attr; unfold_tac = uu___156_13565.unfold_tac; pure_subterms_within_computations = false; simplify = false; erase_universes = uu___156_13565.erase_universes; allow_unbound_universes = uu___156_13565.allow_unbound_universes; reify_ = false; compress_uvars = uu___156_13565.compress_uvars; no_full_norm = true; check_no_uvars = uu___156_13565.check_no_uvars; unmeta = false; unascribe = false; in_full_norm_request = uu___156_13565.in_full_norm_request; weakly_reduce_scrutinee = uu___156_13565.weakly_reduce_scrutinee})
in (

let cfg' = (

let uu___157_13567 = cfg
in {steps = steps'; tcenv = uu___157_13567.tcenv; debug = uu___157_13567.debug; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]; primitive_steps = uu___157_13567.primitive_steps; strong = uu___157_13567.strong; memoize_lazy = uu___157_13567.memoize_lazy; normalize_pure_lets = uu___157_13567.normalize_pure_lets})
in (norm cfg' env [] t1)))
end)
in (rebuild cfg env stack t2))
end
| uu____13568 -> begin
(

let uu____13569 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____13569) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____13611 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.steps.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____13648 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____13648))))
end
| uu____13649 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___158_13653 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___158_13653.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___158_13653.FStar_Syntax_Syntax.residual_flags})))
end
| uu____13654 -> begin
lopt
end)
in ((log cfg (fun uu____13660 -> (

let uu____13661 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____13661))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___159_13670 = cfg
in {steps = uu___159_13670.steps; tcenv = uu___159_13670.tcenv; debug = uu___159_13670.debug; delta_level = uu___159_13670.delta_level; primitive_steps = uu___159_13670.primitive_steps; strong = true; memoize_lazy = uu___159_13670.memoize_lazy; normalize_pure_lets = uu___159_13670.normalize_pure_lets})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Let (uu____13681))::uu____13682 -> begin
(match (cfg.steps.weak) with
| true -> begin
(

let t2 = (match (cfg.steps.in_full_norm_request) with
| true -> begin
(closure_as_term cfg env t1)
end
| uu____13694 -> begin
(

let steps' = (

let uu___156_13696 = cfg.steps
in {beta = uu___156_13696.beta; iota = false; zeta = false; weak = false; hnf = uu___156_13696.hnf; primops = false; do_not_unfold_pure_lets = true; unfold_until = uu___156_13696.unfold_until; unfold_only = uu___156_13696.unfold_only; unfold_fully = uu___156_13696.unfold_fully; unfold_attr = uu___156_13696.unfold_attr; unfold_tac = uu___156_13696.unfold_tac; pure_subterms_within_computations = false; simplify = false; erase_universes = uu___156_13696.erase_universes; allow_unbound_universes = uu___156_13696.allow_unbound_universes; reify_ = false; compress_uvars = uu___156_13696.compress_uvars; no_full_norm = true; check_no_uvars = uu___156_13696.check_no_uvars; unmeta = false; unascribe = false; in_full_norm_request = uu___156_13696.in_full_norm_request; weakly_reduce_scrutinee = uu___156_13696.weakly_reduce_scrutinee})
in (

let cfg' = (

let uu___157_13698 = cfg
in {steps = steps'; tcenv = uu___157_13698.tcenv; debug = uu___157_13698.debug; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]; primitive_steps = uu___157_13698.primitive_steps; strong = uu___157_13698.strong; memoize_lazy = uu___157_13698.memoize_lazy; normalize_pure_lets = uu___157_13698.normalize_pure_lets})
in (norm cfg' env [] t1)))
end)
in (rebuild cfg env stack t2))
end
| uu____13699 -> begin
(

let uu____13700 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____13700) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____13742 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.steps.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____13779 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____13779))))
end
| uu____13780 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___158_13784 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___158_13784.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___158_13784.FStar_Syntax_Syntax.residual_flags})))
end
| uu____13785 -> begin
lopt
end)
in ((log cfg (fun uu____13791 -> (

let uu____13792 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____13792))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___159_13801 = cfg
in {steps = uu___159_13801.steps; tcenv = uu___159_13801.tcenv; debug = uu___159_13801.debug; delta_level = uu___159_13801.delta_level; primitive_steps = uu___159_13801.primitive_steps; strong = true; memoize_lazy = uu___159_13801.memoize_lazy; normalize_pure_lets = uu___159_13801.normalize_pure_lets})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (App (uu____13812))::uu____13813 -> begin
(match (cfg.steps.weak) with
| true -> begin
(

let t2 = (match (cfg.steps.in_full_norm_request) with
| true -> begin
(closure_as_term cfg env t1)
end
| uu____13825 -> begin
(

let steps' = (

let uu___156_13827 = cfg.steps
in {beta = uu___156_13827.beta; iota = false; zeta = false; weak = false; hnf = uu___156_13827.hnf; primops = false; do_not_unfold_pure_lets = true; unfold_until = uu___156_13827.unfold_until; unfold_only = uu___156_13827.unfold_only; unfold_fully = uu___156_13827.unfold_fully; unfold_attr = uu___156_13827.unfold_attr; unfold_tac = uu___156_13827.unfold_tac; pure_subterms_within_computations = false; simplify = false; erase_universes = uu___156_13827.erase_universes; allow_unbound_universes = uu___156_13827.allow_unbound_universes; reify_ = false; compress_uvars = uu___156_13827.compress_uvars; no_full_norm = true; check_no_uvars = uu___156_13827.check_no_uvars; unmeta = false; unascribe = false; in_full_norm_request = uu___156_13827.in_full_norm_request; weakly_reduce_scrutinee = uu___156_13827.weakly_reduce_scrutinee})
in (

let cfg' = (

let uu___157_13829 = cfg
in {steps = steps'; tcenv = uu___157_13829.tcenv; debug = uu___157_13829.debug; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]; primitive_steps = uu___157_13829.primitive_steps; strong = uu___157_13829.strong; memoize_lazy = uu___157_13829.memoize_lazy; normalize_pure_lets = uu___157_13829.normalize_pure_lets})
in (norm cfg' env [] t1)))
end)
in (rebuild cfg env stack t2))
end
| uu____13830 -> begin
(

let uu____13831 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____13831) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____13873 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.steps.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____13910 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____13910))))
end
| uu____13911 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___158_13915 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___158_13915.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___158_13915.FStar_Syntax_Syntax.residual_flags})))
end
| uu____13916 -> begin
lopt
end)
in ((log cfg (fun uu____13922 -> (

let uu____13923 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____13923))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___159_13932 = cfg
in {steps = uu___159_13932.steps; tcenv = uu___159_13932.tcenv; debug = uu___159_13932.debug; delta_level = uu___159_13932.delta_level; primitive_steps = uu___159_13932.primitive_steps; strong = true; memoize_lazy = uu___159_13932.memoize_lazy; normalize_pure_lets = uu___159_13932.normalize_pure_lets})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| (Abs (uu____13943))::uu____13944 -> begin
(match (cfg.steps.weak) with
| true -> begin
(

let t2 = (match (cfg.steps.in_full_norm_request) with
| true -> begin
(closure_as_term cfg env t1)
end
| uu____13960 -> begin
(

let steps' = (

let uu___156_13962 = cfg.steps
in {beta = uu___156_13962.beta; iota = false; zeta = false; weak = false; hnf = uu___156_13962.hnf; primops = false; do_not_unfold_pure_lets = true; unfold_until = uu___156_13962.unfold_until; unfold_only = uu___156_13962.unfold_only; unfold_fully = uu___156_13962.unfold_fully; unfold_attr = uu___156_13962.unfold_attr; unfold_tac = uu___156_13962.unfold_tac; pure_subterms_within_computations = false; simplify = false; erase_universes = uu___156_13962.erase_universes; allow_unbound_universes = uu___156_13962.allow_unbound_universes; reify_ = false; compress_uvars = uu___156_13962.compress_uvars; no_full_norm = true; check_no_uvars = uu___156_13962.check_no_uvars; unmeta = false; unascribe = false; in_full_norm_request = uu___156_13962.in_full_norm_request; weakly_reduce_scrutinee = uu___156_13962.weakly_reduce_scrutinee})
in (

let cfg' = (

let uu___157_13964 = cfg
in {steps = steps'; tcenv = uu___157_13964.tcenv; debug = uu___157_13964.debug; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]; primitive_steps = uu___157_13964.primitive_steps; strong = uu___157_13964.strong; memoize_lazy = uu___157_13964.memoize_lazy; normalize_pure_lets = uu___157_13964.normalize_pure_lets})
in (norm cfg' env [] t1)))
end)
in (rebuild cfg env stack t2))
end
| uu____13965 -> begin
(

let uu____13966 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____13966) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____14008 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.steps.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____14045 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____14045))))
end
| uu____14046 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___158_14050 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___158_14050.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___158_14050.FStar_Syntax_Syntax.residual_flags})))
end
| uu____14051 -> begin
lopt
end)
in ((log cfg (fun uu____14057 -> (

let uu____14058 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____14058))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___159_14067 = cfg
in {steps = uu___159_14067.steps; tcenv = uu___159_14067.tcenv; debug = uu___159_14067.debug; delta_level = uu___159_14067.delta_level; primitive_steps = uu___159_14067.primitive_steps; strong = true; memoize_lazy = uu___159_14067.memoize_lazy; normalize_pure_lets = uu___159_14067.normalize_pure_lets})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end
| [] -> begin
(match (cfg.steps.weak) with
| true -> begin
(

let t2 = (match (cfg.steps.in_full_norm_request) with
| true -> begin
(closure_as_term cfg env t1)
end
| uu____14079 -> begin
(

let steps' = (

let uu___156_14081 = cfg.steps
in {beta = uu___156_14081.beta; iota = false; zeta = false; weak = false; hnf = uu___156_14081.hnf; primops = false; do_not_unfold_pure_lets = true; unfold_until = uu___156_14081.unfold_until; unfold_only = uu___156_14081.unfold_only; unfold_fully = uu___156_14081.unfold_fully; unfold_attr = uu___156_14081.unfold_attr; unfold_tac = uu___156_14081.unfold_tac; pure_subterms_within_computations = false; simplify = false; erase_universes = uu___156_14081.erase_universes; allow_unbound_universes = uu___156_14081.allow_unbound_universes; reify_ = false; compress_uvars = uu___156_14081.compress_uvars; no_full_norm = true; check_no_uvars = uu___156_14081.check_no_uvars; unmeta = false; unascribe = false; in_full_norm_request = uu___156_14081.in_full_norm_request; weakly_reduce_scrutinee = uu___156_14081.weakly_reduce_scrutinee})
in (

let cfg' = (

let uu___157_14083 = cfg
in {steps = steps'; tcenv = uu___157_14083.tcenv; debug = uu___157_14083.debug; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]; primitive_steps = uu___157_14083.primitive_steps; strong = uu___157_14083.strong; memoize_lazy = uu___157_14083.memoize_lazy; normalize_pure_lets = uu___157_14083.normalize_pure_lets})
in (norm cfg' env [] t1)))
end)
in (rebuild cfg env stack t2))
end
| uu____14084 -> begin
(

let uu____14085 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____14085) with
| (bs1, body1, opening) -> begin
(

let env' = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____14127 -> (dummy)::env1) env))
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let rct = (match (cfg.steps.check_no_uvars) with
| true -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun t2 -> (

let uu____14164 = (FStar_Syntax_Subst.subst opening t2)
in (norm cfg env' [] uu____14164))))
end
| uu____14165 -> begin
(FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (FStar_Syntax_Subst.subst opening))
end)
in FStar_Pervasives_Native.Some ((

let uu___158_14169 = rc
in {FStar_Syntax_Syntax.residual_effect = uu___158_14169.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = rct; FStar_Syntax_Syntax.residual_flags = uu___158_14169.FStar_Syntax_Syntax.residual_flags})))
end
| uu____14170 -> begin
lopt
end)
in ((log cfg (fun uu____14176 -> (

let uu____14177 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs1))
in (FStar_Util.print1 "\tShifted %s dummies\n" uu____14177))));
(

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___159_14186 = cfg
in {steps = uu___159_14186.steps; tcenv = uu___159_14186.tcenv; debug = uu___159_14186.debug; delta_level = uu___159_14186.delta_level; primitive_steps = uu___159_14186.primitive_steps; strong = true; memoize_lazy = uu___159_14186.memoize_lazy; normalize_pure_lets = uu___159_14186.normalize_pure_lets})
in (norm cfg1 env' ((Abs (((env), (bs1), (env'), (lopt1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1)));
)))
end))
end)
end)
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let stack1 = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____14235 stack1 -> (match (uu____14235) with
| (a, aq) -> begin
(

let uu____14247 = (

let uu____14248 = (

let uu____14255 = (

let uu____14256 = (

let uu____14287 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (a), (uu____14287), (false)))
in Clos (uu____14256))
in ((uu____14255), (aq), (t1.FStar_Syntax_Syntax.pos)))
in Arg (uu____14248))
in (uu____14247)::stack1)
end)) args))
in ((log cfg (fun uu____14419 -> (

let uu____14420 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" uu____14420))));
(norm cfg env stack1 head1);
))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
(match (cfg.steps.weak) with
| true -> begin
(match (((env), (stack))) with
| ([], []) -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let t2 = (mk (FStar_Syntax_Syntax.Tm_refine ((((

let uu___160_14456 = x
in {FStar_Syntax_Syntax.ppname = uu___160_14456.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___160_14456.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t2)))
end
| uu____14457 -> begin
(

let uu____14462 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____14462))
end)
end
| uu____14463 -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let uu____14465 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____14465) with
| (closing, f1) -> begin
(

let f2 = (norm cfg ((dummy)::env) [] f1)
in (

let t2 = (

let uu____14496 = (

let uu____14497 = (

let uu____14504 = (FStar_Syntax_Subst.close closing f2)
in (((

let uu___161_14506 = x
in {FStar_Syntax_Syntax.ppname = uu___161_14506.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___161_14506.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (uu____14504)))
in FStar_Syntax_Syntax.Tm_refine (uu____14497))
in (mk uu____14496 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t2)))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (cfg.steps.weak) with
| true -> begin
(

let uu____14525 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____14525))
end
| uu____14526 -> begin
(

let uu____14527 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____14527) with
| (bs1, c1) -> begin
(

let c2 = (

let uu____14535 = (FStar_All.pipe_right bs1 (FStar_List.fold_left (fun env1 uu____14559 -> (dummy)::env1) env))
in (norm_comp cfg uu____14535 c1))
in (

let t2 = (

let uu____14581 = (norm_binders cfg env bs1)
in (FStar_Syntax_Util.arrow uu____14581 c2))
in (rebuild cfg env stack t2)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) when cfg.steps.unascribe -> begin
(norm cfg env stack t11)
end
| FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) -> begin
(match (stack) with
| (Match (uu____14692))::uu____14693 -> begin
((log cfg (fun uu____14706 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| (Arg (uu____14707))::uu____14708 -> begin
((log cfg (fun uu____14719 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| (App (uu____14720, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.pos = uu____14721; FStar_Syntax_Syntax.vars = uu____14722}, uu____14723, uu____14724))::uu____14725 -> begin
((log cfg (fun uu____14734 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| (MemoLazy (uu____14735))::uu____14736 -> begin
((log cfg (fun uu____14747 -> (FStar_Util.print_string "+++ Dropping ascription \n")));
(norm cfg env stack t11);
)
end
| uu____14748 -> begin
((log cfg (fun uu____14751 -> (FStar_Util.print_string "+++ Keeping ascription \n")));
(

let t12 = (norm cfg env [] t11)
in ((log cfg (fun uu____14755 -> (FStar_Util.print_string "+++ Normalizing ascription \n")));
(

let tc1 = (match (tc) with
| FStar_Util.Inl (t2) -> begin
(

let uu____14772 = (norm cfg env [] t2)
in FStar_Util.Inl (uu____14772))
end
| FStar_Util.Inr (c) -> begin
(

let uu____14780 = (norm_comp cfg env c)
in FStar_Util.Inr (uu____14780))
end)
in (

let tacopt1 = (FStar_Util.map_opt tacopt (norm cfg env []))
in (match (stack) with
| (Cfg (cfg1))::stack1 -> begin
(

let t2 = (

let uu____14793 = (

let uu____14794 = (

let uu____14821 = (FStar_Syntax_Util.unascribe t12)
in ((uu____14821), (((tc1), (tacopt1))), (l)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____14794))
in (mk uu____14793 t1.FStar_Syntax_Syntax.pos))
in (norm cfg1 env stack1 t2))
end
| uu____14840 -> begin
(

let uu____14841 = (

let uu____14842 = (

let uu____14843 = (

let uu____14870 = (FStar_Syntax_Util.unascribe t12)
in ((uu____14870), (((tc1), (tacopt1))), (l)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____14843))
in (mk uu____14842 t1.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack uu____14841))
end)));
));
)
end)
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let stack1 = (Match (((env), (branches), (cfg), (t1.FStar_Syntax_Syntax.pos))))::stack
in (

let cfg1 = (match (((cfg.steps.iota && cfg.steps.weakly_reduce_scrutinee) && (not (cfg.steps.weak)))) with
| true -> begin
(

let uu___162_14947 = cfg
in {steps = (

let uu___163_14950 = cfg.steps
in {beta = uu___163_14950.beta; iota = uu___163_14950.iota; zeta = uu___163_14950.zeta; weak = true; hnf = uu___163_14950.hnf; primops = uu___163_14950.primops; do_not_unfold_pure_lets = uu___163_14950.do_not_unfold_pure_lets; unfold_until = uu___163_14950.unfold_until; unfold_only = uu___163_14950.unfold_only; unfold_fully = uu___163_14950.unfold_fully; unfold_attr = uu___163_14950.unfold_attr; unfold_tac = uu___163_14950.unfold_tac; pure_subterms_within_computations = uu___163_14950.pure_subterms_within_computations; simplify = uu___163_14950.simplify; erase_universes = uu___163_14950.erase_universes; allow_unbound_universes = uu___163_14950.allow_unbound_universes; reify_ = uu___163_14950.reify_; compress_uvars = uu___163_14950.compress_uvars; no_full_norm = uu___163_14950.no_full_norm; check_no_uvars = uu___163_14950.check_no_uvars; unmeta = uu___163_14950.unmeta; unascribe = uu___163_14950.unascribe; in_full_norm_request = uu___163_14950.in_full_norm_request; weakly_reduce_scrutinee = uu___163_14950.weakly_reduce_scrutinee}); tcenv = uu___162_14947.tcenv; debug = uu___162_14947.debug; delta_level = uu___162_14947.delta_level; primitive_steps = uu___162_14947.primitive_steps; strong = uu___162_14947.strong; memoize_lazy = uu___162_14947.memoize_lazy; normalize_pure_lets = uu___162_14947.normalize_pure_lets})
end
| uu____14951 -> begin
cfg
end)
in (norm cfg1 env stack1 head1)))
end
| FStar_Syntax_Syntax.Tm_let ((b, lbs), lbody) when ((FStar_Syntax_Syntax.is_top_level lbs) && cfg.steps.compress_uvars) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____14986 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____14986) with
| (openings, lbunivs) -> begin
(

let cfg1 = (

let uu___164_15006 = cfg
in (

let uu____15007 = (FStar_TypeChecker_Env.push_univ_vars cfg.tcenv lbunivs)
in {steps = uu___164_15006.steps; tcenv = uu____15007; debug = uu___164_15006.debug; delta_level = uu___164_15006.delta_level; primitive_steps = uu___164_15006.primitive_steps; strong = uu___164_15006.strong; memoize_lazy = uu___164_15006.memoize_lazy; normalize_pure_lets = uu___164_15006.normalize_pure_lets}))
in (

let norm1 = (fun t2 -> (

let uu____15014 = (

let uu____15015 = (FStar_Syntax_Subst.subst openings t2)
in (norm cfg1 env [] uu____15015))
in (FStar_Syntax_Subst.close_univ_vars lbunivs uu____15014)))
in (

let lbtyp = (norm1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbdef = (norm1 lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___165_15018 = lb
in {FStar_Syntax_Syntax.lbname = uu___165_15018.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = lbunivs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = uu___165_15018.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___165_15018.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___165_15018.FStar_Syntax_Syntax.lbpos})))))
end)))))
in (

let uu____15019 = (mk (FStar_Syntax_Syntax.Tm_let (((((b), (lbs1))), (lbody)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack uu____15019)))
end
| FStar_Syntax_Syntax.Tm_let ((uu____15030, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____15031); FStar_Syntax_Syntax.lbunivs = uu____15032; FStar_Syntax_Syntax.lbtyp = uu____15033; FStar_Syntax_Syntax.lbeff = uu____15034; FStar_Syntax_Syntax.lbdef = uu____15035; FStar_Syntax_Syntax.lbattrs = uu____15036; FStar_Syntax_Syntax.lbpos = uu____15037})::uu____15038), uu____15039) -> begin
(rebuild cfg env stack t1)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n1 = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in (

let uu____15079 = ((not (cfg.steps.do_not_unfold_pure_lets)) && (((cfg.steps.pure_subterms_within_computations && (FStar_Syntax_Util.has_attribute lb.FStar_Syntax_Syntax.lbattrs FStar_Parser_Const.inline_let_attr)) || ((FStar_Syntax_Util.is_pure_effect n1) && (cfg.normalize_pure_lets || (FStar_Syntax_Util.has_attribute lb.FStar_Syntax_Syntax.lbattrs FStar_Parser_Const.inline_let_attr)))) || ((FStar_Syntax_Util.is_ghost_effect n1) && (not (cfg.steps.pure_subterms_within_computations)))))
in (match (uu____15079) with
| true -> begin
(

let binder = (

let uu____15081 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.mk_binder uu____15081))
in (

let env1 = (

let uu____15091 = (

let uu____15098 = (

let uu____15099 = (

let uu____15130 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (uu____15130), (false)))
in Clos (uu____15099))
in ((FStar_Pervasives_Native.Some (binder)), (uu____15098)))
in (uu____15091)::env)
in ((log cfg (fun uu____15271 -> (FStar_Util.print_string "+++ Reducing Tm_let\n")));
(norm cfg env1 stack body);
)))
end
| uu____15272 -> begin
(match (cfg.steps.weak) with
| true -> begin
((log cfg (fun uu____15275 -> (FStar_Util.print_string "+++ Not touching Tm_let\n")));
(

let uu____15276 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____15276));
)
end
| uu____15277 -> begin
(

let uu____15278 = (

let uu____15283 = (

let uu____15284 = (

let uu____15285 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right uu____15285 FStar_Syntax_Syntax.mk_binder))
in (uu____15284)::[])
in (FStar_Syntax_Subst.open_term uu____15283 body))
in (match (uu____15278) with
| (bs, body1) -> begin
((log cfg (fun uu____15294 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- type")));
(

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let x = (

let uu____15302 = (FStar_List.hd bs)
in (FStar_Pervasives_Native.fst uu____15302))
in FStar_Util.Inl ((

let uu___166_15312 = x
in {FStar_Syntax_Syntax.ppname = uu___166_15312.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___166_15312.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})))
in ((log cfg (fun uu____15315 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- definiens\n")));
(

let lb1 = (

let uu___167_15317 = lb
in (

let uu____15318 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___167_15317.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___167_15317.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____15318; FStar_Syntax_Syntax.lbattrs = uu___167_15317.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___167_15317.FStar_Syntax_Syntax.lbpos}))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env1 uu____15353 -> (dummy)::env1) env))
in (

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (

let uu___168_15376 = cfg
in {steps = uu___168_15376.steps; tcenv = uu___168_15376.tcenv; debug = uu___168_15376.debug; delta_level = uu___168_15376.delta_level; primitive_steps = uu___168_15376.primitive_steps; strong = true; memoize_lazy = uu___168_15376.memoize_lazy; normalize_pure_lets = uu___168_15376.normalize_pure_lets})
in ((log cfg1 (fun uu____15379 -> (FStar_Util.print_string "+++ Normalizing Tm_let -- body\n")));
(norm cfg1 env' ((Let (((env), (bs), (lb1), (t1.FStar_Syntax_Syntax.pos))))::stack1) body1);
)))));
)));
)
end))
end)
end)))
end
| FStar_Syntax_Syntax.Tm_let ((true, lbs), body) when (cfg.steps.compress_uvars || ((not (cfg.steps.zeta)) && cfg.steps.pure_subterms_within_computations)) -> begin
(

let uu____15396 = (FStar_Syntax_Subst.open_let_rec lbs body)
in (match (uu____15396) with
| (lbs1, body1) -> begin
(

let lbs2 = (FStar_List.map (fun lb -> (

let ty = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbname = (

let uu____15432 = (

let uu___169_15433 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___169_15433.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___169_15433.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = ty})
in FStar_Util.Inl (uu____15432))
in (

let uu____15434 = (FStar_Syntax_Util.abs_formals lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____15434) with
| (xs, def_body, lopt) -> begin
(

let xs1 = (norm_binders cfg env xs)
in (

let env1 = (

let uu____15460 = (FStar_List.map (fun uu____15476 -> dummy) lbs1)
in (

let uu____15477 = (

let uu____15486 = (FStar_List.map (fun uu____15506 -> dummy) xs1)
in (FStar_List.append uu____15486 env))
in (FStar_List.append uu____15460 uu____15477)))
in (

let def_body1 = (norm cfg env1 [] def_body)
in (

let lopt1 = (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____15530 = (

let uu___170_15531 = rc
in (

let uu____15532 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env1 []))
in {FStar_Syntax_Syntax.residual_effect = uu___170_15531.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____15532; FStar_Syntax_Syntax.residual_flags = uu___170_15531.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____15530))
end
| uu____15539 -> begin
lopt
end)
in (

let def = (FStar_Syntax_Util.abs xs1 def_body1 lopt1)
in (

let uu___171_15543 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = uu___171_15543.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = ty; FStar_Syntax_Syntax.lbeff = uu___171_15543.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def; FStar_Syntax_Syntax.lbattrs = uu___171_15543.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___171_15543.FStar_Syntax_Syntax.lbpos}))))))
end))))) lbs1)
in (

let env' = (

let uu____15553 = (FStar_List.map (fun uu____15569 -> dummy) lbs2)
in (FStar_List.append uu____15553 env))
in (

let body2 = (norm cfg env' [] body1)
in (

let uu____15577 = (FStar_Syntax_Subst.close_let_rec lbs2 body2)
in (match (uu____15577) with
| (lbs3, body3) -> begin
(

let t2 = (

let uu___172_15593 = t1
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (((((true), (lbs3))), (body3))); FStar_Syntax_Syntax.pos = uu___172_15593.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___172_15593.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack t2))
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (not (cfg.steps.zeta)) -> begin
(

let uu____15620 = (closure_as_term cfg env t1)
in (rebuild cfg env stack uu____15620))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let uu____15639 = (FStar_List.fold_right (fun lb uu____15715 -> (match (uu____15715) with
| (rec_env, memos, i) -> begin
(

let bv = (

let uu___173_15836 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___173_15836.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___173_15836.FStar_Syntax_Syntax.sort})
in (

let f_i = (FStar_Syntax_Syntax.bv_to_tm bv)
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t1.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let rec_env1 = (((FStar_Pervasives_Native.None), (Clos (((env), (fix_f_i), (memo), (true))))))::rec_env
in ((rec_env1), ((memo)::memos), ((i + (Prims.parse_int "1")))))))))
end)) (FStar_Pervasives_Native.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (uu____15639) with
| (rec_env, memos, uu____16145) -> begin
(

let uu____16198 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (FStar_Pervasives_Native.Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (FStar_Pervasives_Native.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env1 -> (

let uu____16587 = (

let uu____16594 = (

let uu____16595 = (

let uu____16626 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (uu____16626), (false)))
in Clos (uu____16595))
in ((FStar_Pervasives_Native.None), (uu____16594)))
in (uu____16587)::env1)) (FStar_Pervasives_Native.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head1, m) -> begin
((log cfg (fun uu____16784 -> (

let uu____16785 = (FStar_Syntax_Print.metadata_to_string m)
in (FStar_Util.print1 ">> metadata = %s\n" uu____16785))));
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m1, t2) -> begin
(reduce_impure_comp cfg env stack head1 (FStar_Util.Inl (m1)) t2)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) -> begin
(reduce_impure_comp cfg env stack head1 (FStar_Util.Inr (((m1), (m')))) t2)
end
| uu____16807 -> begin
(match (cfg.steps.unmeta) with
| true -> begin
(norm cfg env stack head1)
end
| uu____16808 -> begin
(match (stack) with
| (uu____16809)::uu____16810 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____16815) -> begin
(norm cfg env ((Meta (((env), (m), (r))))::stack) head1)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args1 = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((env), (FStar_Syntax_Syntax.Meta_pattern (args1)), (t1.FStar_Syntax_Syntax.pos))))::stack) head1))
end
| uu____16838 -> begin
(norm cfg env stack head1)
end)
end
| [] -> begin
(

let head2 = (norm cfg env [] head1)
in (

let m1 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let uu____16852 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (uu____16852))
end
| uu____16863 -> begin
m
end)
in (

let t2 = (mk (FStar_Syntax_Syntax.Tm_meta (((head2), (m1)))) t1.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t2))))
end)
end)
end);
)
end
| FStar_Syntax_Syntax.Tm_delayed (uu____16867) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (norm cfg env stack t2))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____16893) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uu____16911) -> begin
(match (cfg.steps.check_no_uvars) with
| true -> begin
(

let uu____16928 = (

let uu____16929 = (FStar_Range.string_of_range t2.FStar_Syntax_Syntax.pos)
in (

let uu____16930 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "(%s) CheckNoUvars: Unexpected unification variable remains: %s" uu____16929 uu____16930)))
in (failwith uu____16928))
end
| uu____16931 -> begin
(rebuild cfg env stack t2)
end)
end
| uu____16932 -> begin
(norm cfg env stack t2)
end))
end);
)))
and do_unfold_fv : cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.qninfo  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t0 qninfo f -> (

let r_env = (

let uu____16942 = (FStar_Syntax_Syntax.range_of_fv f)
in (FStar_TypeChecker_Env.set_range cfg.tcenv uu____16942))
in (

let uu____16943 = (FStar_TypeChecker_Env.lookup_definition_qninfo cfg.delta_level f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v qninfo)
in (match (uu____16943) with
| FStar_Pervasives_Native.None -> begin
((log cfg (fun uu____16956 -> (FStar_Util.print "Tm_fvar case 2\n" [])));
(rebuild cfg env stack t0);
)
end
| FStar_Pervasives_Native.Some (us, t) -> begin
((log cfg (fun uu____16967 -> (

let uu____16968 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____16969 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" uu____16968 uu____16969)))));
(

let t1 = (match (((Prims.op_Equality cfg.steps.unfold_until (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant))) && (not (cfg.steps.unfold_tac)))) with
| true -> begin
t
end
| uu____16973 -> begin
(

let uu____16974 = (FStar_Ident.range_of_lid f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Subst.set_use_range uu____16974 t))
end)
in (

let n1 = (FStar_List.length us)
in (match ((n1 > (Prims.parse_int "0"))) with
| true -> begin
(match (stack) with
| (UnivArgs (us', uu____16983))::stack1 -> begin
(

let env1 = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env1 u -> (((FStar_Pervasives_Native.None), (Univ (u))))::env1) env))
in (norm cfg env1 stack1 t1))
end
| uu____17038 when (cfg.steps.erase_universes || cfg.steps.allow_unbound_universes) -> begin
(norm cfg env stack t1)
end
| uu____17041 -> begin
(

let uu____17044 = (

let uu____17045 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" uu____17045))
in (failwith uu____17044))
end)
end
| uu____17046 -> begin
(norm cfg env stack t1)
end)));
)
end))))
and reduce_impure_comp : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.monad_name, (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name)) FStar_Util.either  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun cfg env stack head1 m t -> (

let t1 = (norm cfg env [] t)
in (

let stack1 = (Cfg (cfg))::stack
in (

let cfg1 = (match (cfg.steps.pure_subterms_within_computations) with
| true -> begin
(

let new_steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::(Inlining)::[]
in (

let uu___174_17069 = cfg
in (

let uu____17070 = (FStar_List.fold_right fstep_add_one new_steps cfg.steps)
in {steps = uu____17070; tcenv = uu___174_17069.tcenv; debug = uu___174_17069.debug; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]; primitive_steps = uu___174_17069.primitive_steps; strong = uu___174_17069.strong; memoize_lazy = uu___174_17069.memoize_lazy; normalize_pure_lets = uu___174_17069.normalize_pure_lets})))
end
| uu____17071 -> begin
(

let uu___175_17072 = cfg
in {steps = (

let uu___176_17075 = cfg.steps
in {beta = uu___176_17075.beta; iota = uu___176_17075.iota; zeta = false; weak = uu___176_17075.weak; hnf = uu___176_17075.hnf; primops = uu___176_17075.primops; do_not_unfold_pure_lets = uu___176_17075.do_not_unfold_pure_lets; unfold_until = uu___176_17075.unfold_until; unfold_only = uu___176_17075.unfold_only; unfold_fully = uu___176_17075.unfold_fully; unfold_attr = uu___176_17075.unfold_attr; unfold_tac = uu___176_17075.unfold_tac; pure_subterms_within_computations = uu___176_17075.pure_subterms_within_computations; simplify = uu___176_17075.simplify; erase_universes = uu___176_17075.erase_universes; allow_unbound_universes = uu___176_17075.allow_unbound_universes; reify_ = uu___176_17075.reify_; compress_uvars = uu___176_17075.compress_uvars; no_full_norm = uu___176_17075.no_full_norm; check_no_uvars = uu___176_17075.check_no_uvars; unmeta = uu___176_17075.unmeta; unascribe = uu___176_17075.unascribe; in_full_norm_request = uu___176_17075.in_full_norm_request; weakly_reduce_scrutinee = uu___176_17075.weakly_reduce_scrutinee}); tcenv = uu___175_17072.tcenv; debug = uu___175_17072.debug; delta_level = uu___175_17072.delta_level; primitive_steps = uu___175_17072.primitive_steps; strong = uu___175_17072.strong; memoize_lazy = uu___175_17072.memoize_lazy; normalize_pure_lets = uu___175_17072.normalize_pure_lets})
end)
in (

let metadata = (match (m) with
| FStar_Util.Inl (m1) -> begin
FStar_Syntax_Syntax.Meta_monadic (((m1), (t1)))
end
| FStar_Util.Inr (m1, m') -> begin
FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m'), (t1)))
end)
in (norm cfg1 env ((Meta (((env), (metadata), (head1.FStar_Syntax_Syntax.pos))))::stack1) head1))))))
and do_reify_monadic : (unit  ->  FStar_Syntax_Syntax.term)  ->  cfg  ->  env  ->  stack_elt Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun fallback cfg env stack head1 m t -> (

let head0 = head1
in (

let head2 = (FStar_Syntax_Util.unascribe head1)
in ((log cfg (fun uu____17105 -> (

let uu____17106 = (FStar_Syntax_Print.tag_of_term head2)
in (

let uu____17107 = (FStar_Syntax_Print.term_to_string head2)
in (FStar_Util.print2 "Reifying: (%s) %s\n" uu____17106 uu____17107)))));
(

let head3 = (FStar_Syntax_Util.unmeta_safe head2)
in (

let uu____17109 = (

let uu____17110 = (FStar_Syntax_Subst.compress head3)
in uu____17110.FStar_Syntax_Syntax.n)
in (match (uu____17109) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (

let uu____17128 = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m)
in (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv uu____17128))
in (

let uu____17129 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____17129) with
| (uu____17130, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____17136) -> begin
(failwith "Cannot reify a top-level let binding")
end
| FStar_Util.Inl (x) -> begin
(

let is_return = (fun e -> (

let uu____17146 = (

let uu____17147 = (FStar_Syntax_Subst.compress e)
in uu____17147.FStar_Syntax_Syntax.n)
in (match (uu____17146) with
| FStar_Syntax_Syntax.Tm_meta (e1, FStar_Syntax_Syntax.Meta_monadic (uu____17153, uu____17154)) -> begin
(

let uu____17163 = (

let uu____17164 = (FStar_Syntax_Subst.compress e1)
in uu____17164.FStar_Syntax_Syntax.n)
in (match (uu____17163) with
| FStar_Syntax_Syntax.Tm_meta (e2, FStar_Syntax_Syntax.Meta_monadic_lift (uu____17170, msrc, uu____17172)) when (FStar_Syntax_Util.is_pure_effect msrc) -> begin
(

let uu____17181 = (FStar_Syntax_Subst.compress e2)
in FStar_Pervasives_Native.Some (uu____17181))
end
| uu____17182 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____17183 -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____17184 = (is_return lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____17184) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let lb1 = (

let uu___177_17189 = lb
in {FStar_Syntax_Syntax.lbname = uu___177_17189.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___177_17189.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___177_17189.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu___177_17189.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___177_17189.FStar_Syntax_Syntax.lbpos})
in (

let uu____17190 = (FStar_List.tl stack)
in (

let uu____17191 = (

let uu____17192 = (

let uu____17199 = (

let uu____17200 = (

let uu____17213 = (FStar_Syntax_Util.mk_reify body)
in ((((false), ((lb1)::[]))), (uu____17213)))
in FStar_Syntax_Syntax.Tm_let (uu____17200))
in (FStar_Syntax_Syntax.mk uu____17199))
in (uu____17192 FStar_Pervasives_Native.None head3.FStar_Syntax_Syntax.pos))
in (norm cfg env uu____17190 uu____17191))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____17229 = (

let uu____17230 = (is_return body)
in (match (uu____17230) with
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_bvar (y); FStar_Syntax_Syntax.pos = uu____17234; FStar_Syntax_Syntax.vars = uu____17235}) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| uu____17240 -> begin
false
end))
in (match (uu____17229) with
| true -> begin
(norm cfg env stack lb.FStar_Syntax_Syntax.lbdef)
end
| uu____17243 -> begin
(

let rng = head3.FStar_Syntax_Syntax.pos
in (

let head4 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body1 = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify body)
in (

let body_rc = {FStar_Syntax_Syntax.residual_effect = m; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some (t); FStar_Syntax_Syntax.residual_flags = []}
in (

let body2 = (

let uu____17263 = (

let uu____17270 = (

let uu____17271 = (

let uu____17288 = (

let uu____17291 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____17291)::[])
in ((uu____17288), (body1), (FStar_Pervasives_Native.Some (body_rc))))
in FStar_Syntax_Syntax.Tm_abs (uu____17271))
in (FStar_Syntax_Syntax.mk uu____17270))
in (uu____17263 FStar_Pervasives_Native.None body1.FStar_Syntax_Syntax.pos))
in (

let close1 = (closure_as_term cfg env)
in (

let bind_inst = (

let uu____17309 = (

let uu____17310 = (FStar_Syntax_Subst.compress bind_repr)
in uu____17310.FStar_Syntax_Syntax.n)
in (match (uu____17309) with
| FStar_Syntax_Syntax.Tm_uinst (bind1, (uu____17316)::(uu____17317)::[]) -> begin
(

let uu____17324 = (

let uu____17331 = (

let uu____17332 = (

let uu____17339 = (

let uu____17342 = (

let uu____17343 = (close1 lb.FStar_Syntax_Syntax.lbtyp)
in (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv uu____17343))
in (

let uu____17344 = (

let uu____17347 = (

let uu____17348 = (close1 t)
in (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv uu____17348))
in (uu____17347)::[])
in (uu____17342)::uu____17344))
in ((bind1), (uu____17339)))
in FStar_Syntax_Syntax.Tm_uinst (uu____17332))
in (FStar_Syntax_Syntax.mk uu____17331))
in (uu____17324 FStar_Pervasives_Native.None rng))
end
| uu____17356 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let maybe_range_arg = (

let uu____17362 = (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.dm4f_bind_range_attr) ed.FStar_Syntax_Syntax.eff_attrs)
in (match (uu____17362) with
| true -> begin
(

let uu____17365 = (

let uu____17366 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range lb.FStar_Syntax_Syntax.lbpos lb.FStar_Syntax_Syntax.lbpos)
in (FStar_Syntax_Syntax.as_arg uu____17366))
in (

let uu____17367 = (

let uu____17370 = (

let uu____17371 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_range body2.FStar_Syntax_Syntax.pos body2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.as_arg uu____17371))
in (uu____17370)::[])
in (uu____17365)::uu____17367))
end
| uu____17372 -> begin
[]
end))
in (

let reified = (

let uu____17376 = (

let uu____17383 = (

let uu____17384 = (

let uu____17399 = (

let uu____17402 = (

let uu____17405 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____17406 = (

let uu____17409 = (FStar_Syntax_Syntax.as_arg t)
in (uu____17409)::[])
in (uu____17405)::uu____17406))
in (

let uu____17410 = (

let uu____17413 = (

let uu____17416 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____17417 = (

let uu____17420 = (FStar_Syntax_Syntax.as_arg head4)
in (

let uu____17421 = (

let uu____17424 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (

let uu____17425 = (

let uu____17428 = (FStar_Syntax_Syntax.as_arg body2)
in (uu____17428)::[])
in (uu____17424)::uu____17425))
in (uu____17420)::uu____17421))
in (uu____17416)::uu____17417))
in (FStar_List.append maybe_range_arg uu____17413))
in (FStar_List.append uu____17402 uu____17410)))
in ((bind_inst), (uu____17399)))
in FStar_Syntax_Syntax.Tm_app (uu____17384))
in (FStar_Syntax_Syntax.mk uu____17383))
in (uu____17376 FStar_Pervasives_Native.None rng))
in ((log cfg (fun uu____17440 -> (

let uu____17441 = (FStar_Syntax_Print.term_to_string head0)
in (

let uu____17442 = (FStar_Syntax_Print.term_to_string reified)
in (FStar_Util.print2 "Reified (1) <%s> to %s\n" uu____17441 uu____17442)))));
(

let uu____17443 = (FStar_List.tl stack)
in (norm cfg env uu____17443 reified));
))))))))))
end))
end)))
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (head_app, args) -> begin
(

let ed = (

let uu____17467 = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv m)
in (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv uu____17467))
in (

let uu____17468 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____17468) with
| (uu____17469, bind_repr) -> begin
(

let maybe_unfold_action = (fun head4 -> (

let maybe_extract_fv = (fun t1 -> (

let t2 = (

let uu____17508 = (

let uu____17509 = (FStar_Syntax_Subst.compress t1)
in uu____17509.FStar_Syntax_Syntax.n)
in (match (uu____17508) with
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____17515) -> begin
t2
end
| uu____17520 -> begin
head4
end))
in (

let uu____17521 = (

let uu____17522 = (FStar_Syntax_Subst.compress t2)
in uu____17522.FStar_Syntax_Syntax.n)
in (match (uu____17521) with
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
FStar_Pervasives_Native.Some (x)
end
| uu____17528 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____17529 = (maybe_extract_fv head4)
in (match (uu____17529) with
| FStar_Pervasives_Native.Some (x) when (

let uu____17539 = (FStar_Syntax_Syntax.lid_of_fv x)
in (FStar_TypeChecker_Env.is_action cfg.tcenv uu____17539)) -> begin
(

let head5 = (norm cfg env [] head4)
in (

let action_unfolded = (

let uu____17544 = (maybe_extract_fv head5)
in (match (uu____17544) with
| FStar_Pervasives_Native.Some (uu____17549) -> begin
FStar_Pervasives_Native.Some (true)
end
| uu____17550 -> begin
FStar_Pervasives_Native.Some (false)
end))
in ((head5), (action_unfolded))))
end
| uu____17555 -> begin
((head4), (FStar_Pervasives_Native.None))
end))))
in ((

let is_arg_impure = (fun uu____17572 -> (match (uu____17572) with
| (e, q) -> begin
(

let uu____17579 = (

let uu____17580 = (FStar_Syntax_Subst.compress e)
in uu____17580.FStar_Syntax_Syntax.n)
in (match (uu____17579) with
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t')) -> begin
(

let uu____17595 = (FStar_Syntax_Util.is_pure_effect m1)
in (not (uu____17595)))
end
| uu____17596 -> begin
false
end))
end))
in (

let uu____17597 = (

let uu____17598 = (

let uu____17605 = (FStar_Syntax_Syntax.as_arg head_app)
in (uu____17605)::args)
in (FStar_Util.for_some is_arg_impure uu____17598))
in (match (uu____17597) with
| true -> begin
(

let uu____17610 = (

let uu____17611 = (FStar_Syntax_Print.term_to_string head3)
in (FStar_Util.format1 "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n" uu____17611))
in (failwith uu____17610))
end
| uu____17612 -> begin
()
end)));
(

let uu____17613 = (maybe_unfold_action head_app)
in (match (uu____17613) with
| (head_app1, found_action) -> begin
(

let mk1 = (fun tm -> (FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None head3.FStar_Syntax_Syntax.pos))
in (

let body = (mk1 (FStar_Syntax_Syntax.Tm_app (((head_app1), (args)))))
in (

let body1 = (match (found_action) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Util.mk_reify body)
end
| FStar_Pervasives_Native.Some (false) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))))
end
| FStar_Pervasives_Native.Some (true) -> begin
body
end)
in ((log cfg (fun uu____17656 -> (

let uu____17657 = (FStar_Syntax_Print.term_to_string head0)
in (

let uu____17658 = (FStar_Syntax_Print.term_to_string body1)
in (FStar_Util.print2 "Reified (2) <%s> to %s\n" uu____17657 uu____17658)))));
(

let uu____17659 = (FStar_List.tl stack)
in (norm cfg env uu____17659 body1));
))))
end));
))
end)))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (uu____17661)) -> begin
(do_reify_monadic fallback cfg env stack e m t)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, t')) -> begin
(

let lifted = (

let uu____17685 = (closure_as_term cfg env t')
in (reify_lift cfg e msrc mtgt uu____17685))
in ((log cfg (fun uu____17689 -> (

let uu____17690 = (FStar_Syntax_Print.term_to_string lifted)
in (FStar_Util.print1 "Reified lift to (2): %s\n" uu____17690))));
(

let uu____17691 = (FStar_List.tl stack)
in (norm cfg env uu____17691 lifted));
))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let branches1 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____17812 -> (match (uu____17812) with
| (pat, wopt, tm) -> begin
(

let uu____17860 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (uu____17860)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches1)))) head3.FStar_Syntax_Syntax.pos)
in (

let uu____17892 = (FStar_List.tl stack)
in (norm cfg env uu____17892 tm))))
end
| uu____17893 -> begin
(fallback ())
end)));
))))
and reify_lift : cfg  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg e msrc mtgt t -> (

let env = cfg.tcenv
in ((log cfg (fun uu____17907 -> (

let uu____17908 = (FStar_Ident.string_of_lid msrc)
in (

let uu____17909 = (FStar_Ident.string_of_lid mtgt)
in (

let uu____17910 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17908 uu____17909 uu____17910))))));
(

let uu____17911 = ((FStar_Syntax_Util.is_pure_effect msrc) || (FStar_Syntax_Util.is_div_effect msrc))
in (match (uu____17911) with
| true -> begin
(

let ed = (

let uu____17913 = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv mtgt)
in (FStar_TypeChecker_Env.get_effect_decl env uu____17913))
in (

let uu____17914 = ed.FStar_Syntax_Syntax.return_repr
in (match (uu____17914) with
| (uu____17915, return_repr) -> begin
(

let return_inst = (

let uu____17924 = (

let uu____17925 = (FStar_Syntax_Subst.compress return_repr)
in uu____17925.FStar_Syntax_Syntax.n)
in (match (uu____17924) with
| FStar_Syntax_Syntax.Tm_uinst (return_tm, (uu____17931)::[]) -> begin
(

let uu____17938 = (

let uu____17945 = (

let uu____17946 = (

let uu____17953 = (

let uu____17956 = (env.FStar_TypeChecker_Env.universe_of env t)
in (uu____17956)::[])
in ((return_tm), (uu____17953)))
in FStar_Syntax_Syntax.Tm_uinst (uu____17946))
in (FStar_Syntax_Syntax.mk uu____17945))
in (uu____17938 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end
| uu____17964 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let uu____17967 = (

let uu____17974 = (

let uu____17975 = (

let uu____17990 = (

let uu____17993 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____17994 = (

let uu____17997 = (FStar_Syntax_Syntax.as_arg e)
in (uu____17997)::[])
in (uu____17993)::uu____17994))
in ((return_inst), (uu____17990)))
in FStar_Syntax_Syntax.Tm_app (uu____17975))
in (FStar_Syntax_Syntax.mk uu____17974))
in (uu____17967 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)))
end)))
end
| uu____18005 -> begin
(

let uu____18006 = (FStar_TypeChecker_Env.monad_leq env msrc mtgt)
in (match (uu____18006) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18009 = (

let uu____18010 = (FStar_Ident.text_of_lid msrc)
in (

let uu____18011 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a lift between unrelated effects (%s and %s)" uu____18010 uu____18011)))
in (failwith uu____18009))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____18012; FStar_TypeChecker_Env.mtarget = uu____18013; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____18014; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.None}}) -> begin
(

let uu____18036 = (

let uu____18037 = (FStar_Ident.text_of_lid msrc)
in (

let uu____18038 = (FStar_Ident.text_of_lid mtgt)
in (FStar_Util.format2 "Impossible : trying to reify a non-reifiable lift (from %s to %s)" uu____18037 uu____18038)))
in (failwith uu____18036))
end
| FStar_Pervasives_Native.Some ({FStar_TypeChecker_Env.msource = uu____18039; FStar_TypeChecker_Env.mtarget = uu____18040; FStar_TypeChecker_Env.mlift = {FStar_TypeChecker_Env.mlift_wp = uu____18041; FStar_TypeChecker_Env.mlift_term = FStar_Pervasives_Native.Some (lift)}}) -> begin
(

let uu____18076 = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let uu____18077 = (FStar_Syntax_Util.mk_reify e)
in (lift uu____18076 t FStar_Syntax_Syntax.tun uu____18077)))
end))
end));
)))
and norm_pattern_args : cfg  ->  env  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun uu____18133 -> (match (uu____18133) with
| (a, imp) -> begin
(

let uu____18144 = (norm cfg env [] a)
in ((uu____18144), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> ((log cfg (fun uu____18152 -> (

let uu____18153 = (FStar_Syntax_Print.comp_to_string comp)
in (

let uu____18154 = (FStar_Util.string_of_int (FStar_List.length env))
in (FStar_Util.print2 ">>> %s\nNormComp with with %s env elements" uu____18153 uu____18154)))));
(match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let t1 = (norm cfg env [] t)
in (

let uopt1 = (match (uopt) with
| FStar_Pervasives_Native.Some (u) -> begin
(

let uu____18178 = (norm_universe cfg env u)
in (FStar_All.pipe_left (fun _0_18 -> FStar_Pervasives_Native.Some (_0_18)) uu____18178))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let uu___178_18181 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t1), (uopt1))); FStar_Syntax_Syntax.pos = uu___178_18181.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___178_18181.FStar_Syntax_Syntax.vars})))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let t1 = (norm cfg env [] t)
in (

let uopt1 = (match (uopt) with
| FStar_Pervasives_Native.Some (u) -> begin
(

let uu____18201 = (norm_universe cfg env u)
in (FStar_All.pipe_left (fun _0_19 -> FStar_Pervasives_Native.Some (_0_19)) uu____18201))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
in (

let uu___179_18204 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (((t1), (uopt1))); FStar_Syntax_Syntax.pos = uu___179_18204.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___179_18204.FStar_Syntax_Syntax.vars})))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (FStar_List.mapi (fun idx uu____18239 -> (match (uu____18239) with
| (a, i) -> begin
(

let uu____18250 = (norm cfg env [] a)
in ((uu____18250), (i)))
end)))
in (

let effect_args = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in (

let flags1 = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___93_18268 -> (match (uu___93_18268) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____18272 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (uu____18272))
end
| f -> begin
f
end))))
in (

let comp_univs = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (

let result_typ = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (

let uu___180_18280 = comp
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ((

let uu___181_18283 = ct
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = uu___181_18283.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = effect_args; FStar_Syntax_Syntax.flags = flags1})); FStar_Syntax_Syntax.pos = uu___180_18280.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___180_18280.FStar_Syntax_Syntax.vars}))))))
end);
))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env uu____18286 -> (match (uu____18286) with
| (x, imp) -> begin
(

let uu____18289 = (

let uu___182_18290 = x
in (

let uu____18291 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___182_18290.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___182_18290.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____18291}))
in ((uu____18289), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let uu____18297 = (FStar_List.fold_left (fun uu____18315 b -> (match (uu____18315) with
| (nbs', env1) -> begin
(

let b1 = (norm_binder cfg env1 b)
in (((b1)::nbs'), ((dummy)::env1)))
end)) (([]), (env)) bs)
in (match (uu____18297) with
| (nbs, uu____18355) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option = (fun cfg env lopt -> (match (lopt) with
| FStar_Pervasives_Native.Some (rc) -> begin
(

let flags1 = (filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags)
in (

let uu____18371 = (

let uu___183_18372 = rc
in (

let uu____18373 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (norm cfg env []))
in {FStar_Syntax_Syntax.residual_effect = uu___183_18372.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____18373; FStar_Syntax_Syntax.residual_flags = uu___183_18372.FStar_Syntax_Syntax.residual_flags}))
in FStar_Pervasives_Native.Some (uu____18371)))
end
| uu____18380 -> begin
lopt
end))
and maybe_simplify : cfg  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.option * closure) Prims.list  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack tm -> (

let tm' = (maybe_simplify_aux cfg env stack tm)
in ((match (cfg.debug.b380) with
| true -> begin
(

let uu____18401 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____18402 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n" (match (cfg.steps.simplify) with
| true -> begin
""
end
| uu____18403 -> begin
"NOT "
end) uu____18401 uu____18402)))
end
| uu____18404 -> begin
()
end);
tm';
)))
and maybe_simplify_aux : cfg  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.option * closure) Prims.list  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack tm -> (

let tm1 = (reduce_primops cfg env stack tm)
in (

let uu____18422 = (FStar_All.pipe_left Prims.op_Negation cfg.steps.simplify)
in (match (uu____18422) with
| true -> begin
tm1
end
| uu____18423 -> begin
(

let w = (fun t -> (

let uu___184_18436 = t
in {FStar_Syntax_Syntax.n = uu___184_18436.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = tm1.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___184_18436.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (

let uu____18447 = (

let uu____18448 = (FStar_Syntax_Util.unmeta t)
in uu____18448.FStar_Syntax_Syntax.n)
in (match (uu____18447) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
FStar_Pervasives_Native.Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid) -> begin
FStar_Pervasives_Native.Some (false)
end
| uu____18455 -> begin
FStar_Pervasives_Native.None
end)))
in (

let rec args_are_binders = (fun args bs -> (match (((args), (bs))) with
| (((t, uu____18504))::args1, ((bv, uu____18507))::bs1) -> begin
(

let uu____18541 = (

let uu____18542 = (FStar_Syntax_Subst.compress t)
in uu____18542.FStar_Syntax_Syntax.n)
in (match (uu____18541) with
| FStar_Syntax_Syntax.Tm_name (bv') -> begin
((FStar_Syntax_Syntax.bv_eq bv bv') && (args_are_binders args1 bs1))
end
| uu____18546 -> begin
false
end))
end
| ([], []) -> begin
true
end
| (uu____18567, uu____18568) -> begin
false
end))
in (

let is_applied = (fun bs t -> ((match (cfg.debug.wpe) with
| true -> begin
(

let uu____18609 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____18610 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____18609 uu____18610)))
end
| uu____18611 -> begin
()
end);
(

let uu____18612 = (FStar_Syntax_Util.head_and_args' t)
in (match (uu____18612) with
| (hd1, args) -> begin
(

let uu____18645 = (

let uu____18646 = (FStar_Syntax_Subst.compress hd1)
in uu____18646.FStar_Syntax_Syntax.n)
in (match (uu____18645) with
| FStar_Syntax_Syntax.Tm_name (bv) when (args_are_binders args bs) -> begin
((match (cfg.debug.wpe) with
| true -> begin
(

let uu____18653 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____18654 = (FStar_Syntax_Print.bv_to_string bv)
in (

let uu____18655 = (FStar_Syntax_Print.term_to_string hd1)
in (FStar_Util.print3 "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n" uu____18653 uu____18654 uu____18655))))
end
| uu____18656 -> begin
()
end);
FStar_Pervasives_Native.Some (bv);
)
end
| uu____18657 -> begin
FStar_Pervasives_Native.None
end))
end));
))
in (

let is_applied_maybe_squashed = (fun bs t -> ((match (cfg.debug.wpe) with
| true -> begin
(

let uu____18674 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____18675 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18674 uu____18675)))
end
| uu____18676 -> begin
()
end);
(

let uu____18677 = (FStar_Syntax_Util.is_squash t)
in (match (uu____18677) with
| FStar_Pervasives_Native.Some (uu____18688, t') -> begin
(is_applied bs t')
end
| uu____18700 -> begin
(

let uu____18709 = (FStar_Syntax_Util.is_auto_squash t)
in (match (uu____18709) with
| FStar_Pervasives_Native.Some (uu____18720, t') -> begin
(is_applied bs t')
end
| uu____18732 -> begin
(is_applied bs t)
end))
end));
))
in (

let is_quantified_const = (fun bv phi -> (

let uu____18756 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____18756) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (lid, ((p, uu____18763))::((q, uu____18765))::[])) when (FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid) -> begin
((match (cfg.debug.wpe) with
| true -> begin
(

let uu____18801 = (FStar_Syntax_Print.term_to_string p)
in (

let uu____18802 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print2 "WPE> p = (%s); q = (%s)\n" uu____18801 uu____18802)))
end
| uu____18803 -> begin
()
end);
(

let uu____18804 = (FStar_Syntax_Util.destruct_typ_as_formula p)
in (match (uu____18804) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18809 = (

let uu____18810 = (FStar_Syntax_Subst.compress p)
in uu____18810.FStar_Syntax_Syntax.n)
in (match (uu____18809) with
| FStar_Syntax_Syntax.Tm_bvar (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
((match (cfg.debug.wpe) with
| true -> begin
(FStar_Util.print_string "WPE> Case 1\n")
end
| uu____18817 -> begin
()
end);
(

let uu____18818 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (FStar_Syntax_Util.t_true))))::[]) q)
in FStar_Pervasives_Native.Some (uu____18818));
)
end
| uu____18819 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (lid1, ((p1, uu____18822))::[])) when (FStar_Ident.lid_equals lid1 FStar_Parser_Const.not_lid) -> begin
(

let uu____18847 = (

let uu____18848 = (FStar_Syntax_Subst.compress p1)
in uu____18848.FStar_Syntax_Syntax.n)
in (match (uu____18847) with
| FStar_Syntax_Syntax.Tm_bvar (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
((match (cfg.debug.wpe) with
| true -> begin
(FStar_Util.print_string "WPE> Case 2\n")
end
| uu____18855 -> begin
()
end);
(

let uu____18856 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (FStar_Syntax_Util.t_false))))::[]) q)
in FStar_Pervasives_Native.Some (uu____18856));
)
end
| uu____18857 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (bs, pats, phi1)) -> begin
(

let uu____18861 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____18861) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18866 = (is_applied_maybe_squashed bs phi1)
in (match (uu____18866) with
| FStar_Pervasives_Native.Some (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
((match (cfg.debug.wpe) with
| true -> begin
(FStar_Util.print_string "WPE> Case 3\n")
end
| uu____18873 -> begin
()
end);
(

let ftrue = (FStar_Syntax_Util.abs bs FStar_Syntax_Util.t_true (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.kprop))))
in (

let uu____18875 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (ftrue))))::[]) q)
in FStar_Pervasives_Native.Some (uu____18875)));
)
end
| uu____18876 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (lid1, ((p1, uu____18881))::[])) when (FStar_Ident.lid_equals lid1 FStar_Parser_Const.not_lid) -> begin
(

let uu____18906 = (is_applied_maybe_squashed bs p1)
in (match (uu____18906) with
| FStar_Pervasives_Native.Some (bv') when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
((match (cfg.debug.wpe) with
| true -> begin
(FStar_Util.print_string "WPE> Case 4\n")
end
| uu____18913 -> begin
()
end);
(

let ffalse = (FStar_Syntax_Util.abs bs FStar_Syntax_Util.t_false (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_tot FStar_Syntax_Util.kprop))))
in (

let uu____18915 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((bv), (ffalse))))::[]) q)
in FStar_Pervasives_Native.Some (uu____18915)));
)
end
| uu____18916 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____18919 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____18922 -> begin
FStar_Pervasives_Native.None
end));
)
end
| uu____18925 -> begin
FStar_Pervasives_Native.None
end)))
in (

let is_forall_const = (fun phi -> (

let uu____18938 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____18938) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (((bv, uu____18944))::[], uu____18945, phi')) -> begin
((match (cfg.debug.wpe) with
| true -> begin
(

let uu____18962 = (FStar_Syntax_Print.bv_to_string bv)
in (

let uu____18963 = (FStar_Syntax_Print.term_to_string phi')
in (FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18962 uu____18963)))
end
| uu____18964 -> begin
()
end);
(is_quantified_const bv phi');
)
end
| uu____18965 -> begin
FStar_Pervasives_Native.None
end)))
in (

let is_const_match = (fun phi -> (

let uu____18978 = (

let uu____18979 = (FStar_Syntax_Subst.compress phi)
in uu____18979.FStar_Syntax_Syntax.n)
in (match (uu____18978) with
| FStar_Syntax_Syntax.Tm_match (uu____18984, (br)::brs) -> begin
(

let uu____19051 = br
in (match (uu____19051) with
| (uu____19068, uu____19069, e) -> begin
(

let r = (

let uu____19090 = (simp_t e)
in (match (uu____19090) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (b) -> begin
(

let uu____19096 = (FStar_List.for_all (fun uu____19114 -> (match (uu____19114) with
| (uu____19127, uu____19128, e') -> begin
(

let uu____19142 = (simp_t e')
in (Prims.op_Equality uu____19142 (FStar_Pervasives_Native.Some (b))))
end)) brs)
in (match (uu____19096) with
| true -> begin
FStar_Pervasives_Native.Some (b)
end
| uu____19149 -> begin
FStar_Pervasives_Native.None
end))
end))
in r)
end))
end
| uu____19150 -> begin
FStar_Pervasives_Native.None
end)))
in (

let maybe_auto_squash = (fun t -> (

let uu____19157 = (FStar_Syntax_Util.is_sub_singleton t)
in (match (uu____19157) with
| true -> begin
t
end
| uu____19158 -> begin
(FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero t)
end)))
in (

let squashed_head_un_auto_squash_args = (fun t -> (

let maybe_un_auto_squash_arg = (fun uu____19182 -> (match (uu____19182) with
| (t1, q) -> begin
(

let uu____19195 = (FStar_Syntax_Util.is_auto_squash t1)
in (match (uu____19195) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero, t2) -> begin
((t2), (q))
end
| uu____19223 -> begin
((t1), (q))
end))
end))
in (

let uu____19232 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____19232) with
| (head1, args) -> begin
(

let args1 = (FStar_List.map maybe_un_auto_squash_arg args)
in (FStar_Syntax_Syntax.mk_Tm_app head1 args1 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end))))
in (

let rec clearly_inhabited = (fun ty -> (

let uu____19296 = (

let uu____19297 = (FStar_Syntax_Util.unmeta ty)
in uu____19297.FStar_Syntax_Syntax.n)
in (match (uu____19296) with
| FStar_Syntax_Syntax.Tm_uinst (t, uu____19301) -> begin
(clearly_inhabited t)
end
| FStar_Syntax_Syntax.Tm_arrow (uu____19306, c) -> begin
(clearly_inhabited (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let l = (FStar_Syntax_Syntax.lid_of_fv fv)
in ((((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) || (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid)) || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)))
end
| uu____19326 -> begin
false
end)))
in (

let simplify1 = (fun arg -> (

let uu____19351 = (simp_t (FStar_Pervasives_Native.fst arg))
in ((uu____19351), (arg))))
in (

let uu____19360 = (is_forall_const tm1)
in (match (uu____19360) with
| FStar_Pervasives_Native.Some (tm') -> begin
((match (cfg.debug.wpe) with
| true -> begin
(

let uu____19365 = (FStar_Syntax_Print.term_to_string tm1)
in (

let uu____19366 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print2 "WPE> %s ~> %s\n" uu____19365 uu____19366)))
end
| uu____19367 -> begin
()
end);
(

let uu____19368 = (norm cfg env [] tm')
in (maybe_simplify_aux cfg env stack uu____19368));
)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____19369 = (

let uu____19370 = (FStar_Syntax_Subst.compress tm1)
in uu____19370.FStar_Syntax_Syntax.n)
in (match (uu____19369) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____19374; FStar_Syntax_Syntax.vars = uu____19375}, uu____19376); FStar_Syntax_Syntax.pos = uu____19377; FStar_Syntax_Syntax.vars = uu____19378}, args) -> begin
(

let uu____19404 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____19404) with
| true -> begin
(

let uu____19405 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____19405) with
| ((FStar_Pervasives_Native.Some (true), uu____19452))::((uu____19453, (arg, uu____19455)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____19504, (arg, uu____19506)))::((FStar_Pervasives_Native.Some (true), uu____19507))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (false), uu____19556))::(uu____19557)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____19608)::((FStar_Pervasives_Native.Some (false), uu____19609))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____19660 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19673 -> begin
(

let uu____19674 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____19674) with
| true -> begin
(

let uu____19675 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____19675) with
| ((FStar_Pervasives_Native.Some (true), uu____19722))::(uu____19723)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____19774)::((FStar_Pervasives_Native.Some (true), uu____19775))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____19826))::((uu____19827, (arg, uu____19829)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____19878, (arg, uu____19880)))::((FStar_Pervasives_Native.Some (false), uu____19881))::[] -> begin
(maybe_auto_squash arg)
end
| uu____19930 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____19943 -> begin
(

let uu____19944 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____19944) with
| true -> begin
(

let uu____19945 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____19945) with
| (uu____19992)::((FStar_Pervasives_Native.Some (true), uu____19993))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____20044))::(uu____20045)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____20096))::((uu____20097, (arg, uu____20099)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____20148, (p, uu____20150)))::((uu____20151, (q, uu____20153)))::[] -> begin
(

let uu____20200 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____20200) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20201 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____20202 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____20215 -> begin
(

let uu____20216 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid)
in (match (uu____20216) with
| true -> begin
(

let uu____20217 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____20217) with
| ((FStar_Pervasives_Native.Some (true), uu____20264))::((FStar_Pervasives_Native.Some (true), uu____20265))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____20316))::((FStar_Pervasives_Native.Some (false), uu____20317))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____20368))::((FStar_Pervasives_Native.Some (false), uu____20369))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____20420))::((FStar_Pervasives_Native.Some (true), uu____20421))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((uu____20472, (arg, uu____20474)))::((FStar_Pervasives_Native.Some (true), uu____20475))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (true), uu____20524))::((uu____20525, (arg, uu____20527)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____20576, (arg, uu____20578)))::((FStar_Pervasives_Native.Some (false), uu____20579))::[] -> begin
(

let uu____20628 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____20628))
end
| ((FStar_Pervasives_Native.Some (false), uu____20629))::((uu____20630, (arg, uu____20632)))::[] -> begin
(

let uu____20681 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____20681))
end
| ((uu____20682, (p, uu____20684)))::((uu____20685, (q, uu____20687)))::[] -> begin
(

let uu____20734 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____20734) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20735 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____20736 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____20749 -> begin
(

let uu____20750 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____20750) with
| true -> begin
(

let uu____20751 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____20751) with
| ((FStar_Pervasives_Native.Some (true), uu____20798))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____20829))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20860 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____20873 -> begin
(

let uu____20874 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____20874) with
| true -> begin
(match (args) with
| ((t, uu____20876))::[] -> begin
(

let uu____20893 = (

let uu____20894 = (FStar_Syntax_Subst.compress t)
in uu____20894.FStar_Syntax_Syntax.n)
in (match (uu____20893) with
| FStar_Syntax_Syntax.Tm_abs ((uu____20897)::[], body, uu____20899) -> begin
(

let uu____20926 = (simp_t body)
in (match (uu____20926) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____20929 -> begin
tm1
end))
end
| uu____20932 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____20934))))::((t, uu____20936))::[] -> begin
(

let uu____20975 = (

let uu____20976 = (FStar_Syntax_Subst.compress t)
in uu____20976.FStar_Syntax_Syntax.n)
in (match (uu____20975) with
| FStar_Syntax_Syntax.Tm_abs ((uu____20979)::[], body, uu____20981) -> begin
(

let uu____21008 = (simp_t body)
in (match (uu____21008) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| FStar_Pervasives_Native.Some (false) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____21011 -> begin
tm1
end))
end
| uu____21014 -> begin
tm1
end))
end
| uu____21015 -> begin
tm1
end)
end
| uu____21024 -> begin
(

let uu____21025 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____21025) with
| true -> begin
(match (args) with
| ((t, uu____21027))::[] -> begin
(

let uu____21044 = (

let uu____21045 = (FStar_Syntax_Subst.compress t)
in uu____21045.FStar_Syntax_Syntax.n)
in (match (uu____21044) with
| FStar_Syntax_Syntax.Tm_abs ((uu____21048)::[], body, uu____21050) -> begin
(

let uu____21077 = (simp_t body)
in (match (uu____21077) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____21080 -> begin
tm1
end))
end
| uu____21083 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____21085))))::((t, uu____21087))::[] -> begin
(

let uu____21126 = (

let uu____21127 = (FStar_Syntax_Subst.compress t)
in uu____21127.FStar_Syntax_Syntax.n)
in (match (uu____21126) with
| FStar_Syntax_Syntax.Tm_abs ((uu____21130)::[], body, uu____21132) -> begin
(

let uu____21159 = (simp_t body)
in (match (uu____21159) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| FStar_Pervasives_Native.Some (true) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____21162 -> begin
tm1
end))
end
| uu____21165 -> begin
tm1
end))
end
| uu____21166 -> begin
tm1
end)
end
| uu____21175 -> begin
(

let uu____21176 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2p_lid)
in (match (uu____21176) with
| true -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true)); FStar_Syntax_Syntax.pos = uu____21177; FStar_Syntax_Syntax.vars = uu____21178}, uu____21179))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false)); FStar_Syntax_Syntax.pos = uu____21196; FStar_Syntax_Syntax.vars = uu____21197}, uu____21198))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____21215 -> begin
tm1
end)
end
| uu____21224 -> begin
(

let uu____21225 = (FStar_Syntax_Util.is_auto_squash tm1)
in (match (uu____21225) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero, t) when (FStar_Syntax_Util.is_sub_singleton t) -> begin
t
end
| uu____21245 -> begin
(reduce_equality cfg env stack tm1)
end))
end))
end))
end))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____21255; FStar_Syntax_Syntax.vars = uu____21256}, args) -> begin
(

let uu____21278 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.and_lid)
in (match (uu____21278) with
| true -> begin
(

let uu____21279 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____21279) with
| ((FStar_Pervasives_Native.Some (true), uu____21326))::((uu____21327, (arg, uu____21329)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____21378, (arg, uu____21380)))::((FStar_Pervasives_Native.Some (true), uu____21381))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (false), uu____21430))::(uu____21431)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (uu____21482)::((FStar_Pervasives_Native.Some (false), uu____21483))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____21534 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____21547 -> begin
(

let uu____21548 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.or_lid)
in (match (uu____21548) with
| true -> begin
(

let uu____21549 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____21549) with
| ((FStar_Pervasives_Native.Some (true), uu____21596))::(uu____21597)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (uu____21648)::((FStar_Pervasives_Native.Some (true), uu____21649))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____21700))::((uu____21701, (arg, uu____21703)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____21752, (arg, uu____21754)))::((FStar_Pervasives_Native.Some (false), uu____21755))::[] -> begin
(maybe_auto_squash arg)
end
| uu____21804 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____21817 -> begin
(

let uu____21818 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.imp_lid)
in (match (uu____21818) with
| true -> begin
(

let uu____21819 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____21819) with
| (uu____21866)::((FStar_Pervasives_Native.Some (true), uu____21867))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____21918))::(uu____21919)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____21970))::((uu____21971, (arg, uu____21973)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____22022, (p, uu____22024)))::((uu____22025, (q, uu____22027)))::[] -> begin
(

let uu____22074 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____22074) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____22075 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____22076 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____22089 -> begin
(

let uu____22090 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.iff_lid)
in (match (uu____22090) with
| true -> begin
(

let uu____22091 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____22091) with
| ((FStar_Pervasives_Native.Some (true), uu____22138))::((FStar_Pervasives_Native.Some (true), uu____22139))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (false), uu____22190))::((FStar_Pervasives_Native.Some (false), uu____22191))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| ((FStar_Pervasives_Native.Some (true), uu____22242))::((FStar_Pervasives_Native.Some (false), uu____22243))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____22294))::((FStar_Pervasives_Native.Some (true), uu____22295))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((uu____22346, (arg, uu____22348)))::((FStar_Pervasives_Native.Some (true), uu____22349))::[] -> begin
(maybe_auto_squash arg)
end
| ((FStar_Pervasives_Native.Some (true), uu____22398))::((uu____22399, (arg, uu____22401)))::[] -> begin
(maybe_auto_squash arg)
end
| ((uu____22450, (arg, uu____22452)))::((FStar_Pervasives_Native.Some (false), uu____22453))::[] -> begin
(

let uu____22502 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____22502))
end
| ((FStar_Pervasives_Native.Some (false), uu____22503))::((uu____22504, (arg, uu____22506)))::[] -> begin
(

let uu____22555 = (FStar_Syntax_Util.mk_neg arg)
in (maybe_auto_squash uu____22555))
end
| ((uu____22556, (p, uu____22558)))::((uu____22559, (q, uu____22561)))::[] -> begin
(

let uu____22608 = (FStar_Syntax_Util.term_eq p q)
in (match (uu____22608) with
| true -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____22609 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____22610 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____22623 -> begin
(

let uu____22624 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.not_lid)
in (match (uu____22624) with
| true -> begin
(

let uu____22625 = (FStar_All.pipe_right args (FStar_List.map simplify1))
in (match (uu____22625) with
| ((FStar_Pervasives_Native.Some (true), uu____22672))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((FStar_Pervasives_Native.Some (false), uu____22703))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____22734 -> begin
(squashed_head_un_auto_squash_args tm1)
end))
end
| uu____22747 -> begin
(

let uu____22748 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid)
in (match (uu____22748) with
| true -> begin
(match (args) with
| ((t, uu____22750))::[] -> begin
(

let uu____22767 = (

let uu____22768 = (FStar_Syntax_Subst.compress t)
in uu____22768.FStar_Syntax_Syntax.n)
in (match (uu____22767) with
| FStar_Syntax_Syntax.Tm_abs ((uu____22771)::[], body, uu____22773) -> begin
(

let uu____22800 = (simp_t body)
in (match (uu____22800) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____22803 -> begin
tm1
end))
end
| uu____22806 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____22808))))::((t, uu____22810))::[] -> begin
(

let uu____22849 = (

let uu____22850 = (FStar_Syntax_Subst.compress t)
in uu____22850.FStar_Syntax_Syntax.n)
in (match (uu____22849) with
| FStar_Syntax_Syntax.Tm_abs ((uu____22853)::[], body, uu____22855) -> begin
(

let uu____22882 = (simp_t body)
in (match (uu____22882) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| FStar_Pervasives_Native.Some (false) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____22885 -> begin
tm1
end))
end
| uu____22888 -> begin
tm1
end))
end
| uu____22889 -> begin
tm1
end)
end
| uu____22898 -> begin
(

let uu____22899 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid)
in (match (uu____22899) with
| true -> begin
(match (args) with
| ((t, uu____22901))::[] -> begin
(

let uu____22918 = (

let uu____22919 = (FStar_Syntax_Subst.compress t)
in uu____22919.FStar_Syntax_Syntax.n)
in (match (uu____22918) with
| FStar_Syntax_Syntax.Tm_abs ((uu____22922)::[], body, uu____22924) -> begin
(

let uu____22951 = (simp_t body)
in (match (uu____22951) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____22954 -> begin
tm1
end))
end
| uu____22957 -> begin
tm1
end))
end
| ((ty, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____22959))))::((t, uu____22961))::[] -> begin
(

let uu____23000 = (

let uu____23001 = (FStar_Syntax_Subst.compress t)
in uu____23001.FStar_Syntax_Syntax.n)
in (match (uu____23000) with
| FStar_Syntax_Syntax.Tm_abs ((uu____23004)::[], body, uu____23006) -> begin
(

let uu____23033 = (simp_t body)
in (match (uu____23033) with
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| FStar_Pervasives_Native.Some (true) when (clearly_inhabited ty) -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____23036 -> begin
tm1
end))
end
| uu____23039 -> begin
tm1
end))
end
| uu____23040 -> begin
tm1
end)
end
| uu____23049 -> begin
(

let uu____23050 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2p_lid)
in (match (uu____23050) with
| true -> begin
(match (args) with
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true)); FStar_Syntax_Syntax.pos = uu____23051; FStar_Syntax_Syntax.vars = uu____23052}, uu____23053))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false)); FStar_Syntax_Syntax.pos = uu____23070; FStar_Syntax_Syntax.vars = uu____23071}, uu____23072))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____23089 -> begin
tm1
end)
end
| uu____23098 -> begin
(

let uu____23099 = (FStar_Syntax_Util.is_auto_squash tm1)
in (match (uu____23099) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.U_zero, t) when (FStar_Syntax_Util.is_sub_singleton t) -> begin
t
end
| uu____23119 -> begin
(reduce_equality cfg env stack tm1)
end))
end))
end))
end))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(

let uu____23134 = (simp_t t)
in (match (uu____23134) with
| FStar_Pervasives_Native.Some (true) -> begin
bv.FStar_Syntax_Syntax.sort
end
| FStar_Pervasives_Native.Some (false) -> begin
tm1
end
| FStar_Pervasives_Native.None -> begin
tm1
end))
end
| FStar_Syntax_Syntax.Tm_match (uu____23137) -> begin
(

let uu____23160 = (is_const_match tm1)
in (match (uu____23160) with
| FStar_Pervasives_Native.Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| FStar_Pervasives_Native.Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| FStar_Pervasives_Native.None -> begin
tm1
end))
end
| uu____23163 -> begin
tm1
end))
end))))))))))))))
end))))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> ((log cfg (fun uu____23173 -> ((

let uu____23175 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____23176 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____23177 = (FStar_Util.string_of_int (FStar_List.length env))
in (

let uu____23184 = (

let uu____23185 = (

let uu____23188 = (firstn (Prims.parse_int "4") stack)
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____23188))
in (stack_to_string uu____23185))
in (FStar_Util.print4 ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n" uu____23175 uu____23176 uu____23177 uu____23184)))));
(

let uu____23211 = (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("NormRebuild")))
in (match (uu____23211) with
| true -> begin
(

let uu____23212 = (FStar_Syntax_Util.unbound_variables t)
in (match (uu____23212) with
| [] -> begin
()
end
| bvs -> begin
((

let uu____23219 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____23220 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____23221 = (

let uu____23222 = (FStar_All.pipe_right bvs (FStar_List.map FStar_Syntax_Print.bv_to_string))
in (FStar_All.pipe_right uu____23222 (FStar_String.concat ", ")))
in (FStar_Util.print3 "!!! Rebuild (%s) %s, free vars=%s\n" uu____23219 uu____23220 uu____23221))));
(failwith "DIE!");
)
end))
end
| uu____23231 -> begin
()
end));
)));
(

let t1 = (maybe_simplify cfg env stack t)
in (match (stack) with
| [] -> begin
t1
end
| (Debug (tm, time_then))::stack1 -> begin
((match (cfg.debug.print_normalized) with
| true -> begin
(

let time_now = (FStar_Util.now ())
in (

let uu____23240 = (

let uu____23241 = (

let uu____23242 = (FStar_Util.time_diff time_then time_now)
in (FStar_Pervasives_Native.snd uu____23242))
in (FStar_Util.string_of_int uu____23241))
in (

let uu____23247 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____23248 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n" uu____23240 uu____23247 uu____23248)))))
end
| uu____23249 -> begin
()
end);
(rebuild cfg env stack1 t1);
)
end
| (Cfg (cfg1))::stack1 -> begin
(rebuild cfg1 env stack1 t1)
end
| (Meta (uu____23254, m, r))::stack1 -> begin
(

let t2 = (mk (FStar_Syntax_Syntax.Tm_meta (((t1), (m)))) r)
in (rebuild cfg env stack1 t2))
end
| (MemoLazy (r))::stack1 -> begin
((set_memo cfg r ((env), (t1)));
(log cfg (fun uu____23351 -> (

let uu____23352 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "\tSet memo %s\n" uu____23352))));
(rebuild cfg env stack1 t1);
)
end
| (Let (env', bs, lb, r))::stack1 -> begin
(

let body = (FStar_Syntax_Subst.close bs t1)
in (

let t2 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) FStar_Pervasives_Native.None r)
in (rebuild cfg env' stack1 t2)))
end
| (Abs (env', bs, env'', lopt, r))::stack1 -> begin
(

let bs1 = (norm_binders cfg env' bs)
in (

let lopt1 = (norm_lcomp_opt cfg env'' lopt)
in (

let uu____23388 = (

let uu___185_23389 = (FStar_Syntax_Util.abs bs1 t1 lopt1)
in {FStar_Syntax_Syntax.n = uu___185_23389.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___185_23389.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack1 uu____23388))))
end
| (Arg (Univ (uu____23390), uu____23391, uu____23392))::uu____23393 -> begin
(failwith "Impossible")
end
| (Arg (Dummy, uu____23396, uu____23397))::uu____23398 -> begin
(failwith "Impossible")
end
| (UnivArgs (us, r))::stack1 -> begin
(

let t2 = (FStar_Syntax_Syntax.mk_Tm_uinst t1 us)
in (rebuild cfg env stack1 t2))
end
| (Arg (Clos (env_arg, tm, uu____23413, uu____23414), aq, r))::stack1 when (

let uu____23464 = (head_of t1)
in (FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____23464)) -> begin
(

let t2 = (

let uu____23468 = (

let uu____23473 = (

let uu____23474 = (closure_as_term cfg env_arg tm)
in ((uu____23474), (aq)))
in (FStar_Syntax_Syntax.extend_app t1 uu____23473))
in (uu____23468 FStar_Pervasives_Native.None r))
in (rebuild cfg env stack1 t2))
end
| (Arg (Clos (env_arg, tm, m, uu____23480), aq, r))::stack1 -> begin
((log cfg (fun uu____23533 -> (

let uu____23534 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" uu____23534))));
(match ((not (cfg.steps.iota))) with
| true -> begin
(match (cfg.steps.hnf) with
| true -> begin
(

let arg = (closure_as_term cfg env_arg tm)
in (

let t2 = (FStar_Syntax_Syntax.extend_app t1 ((arg), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env_arg stack1 t2)))
end
| uu____23539 -> begin
(

let stack2 = (App (((env), (t1), (aq), (r))))::stack1
in (norm cfg env_arg stack2 tm))
end)
end
| uu____23543 -> begin
(

let uu____23544 = (FStar_ST.op_Bang m)
in (match (uu____23544) with
| FStar_Pervasives_Native.None -> begin
(match (cfg.steps.hnf) with
| true -> begin
(

let arg = (closure_as_term cfg env_arg tm)
in (

let t2 = (FStar_Syntax_Syntax.extend_app t1 ((arg), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env_arg stack1 t2)))
end
| uu____23702 -> begin
(

let stack2 = (MemoLazy (m))::(App (((env), (t1), (aq), (r))))::stack1
in (norm cfg env_arg stack2 tm))
end)
end
| FStar_Pervasives_Native.Some (uu____23811, a) -> begin
(

let t2 = (FStar_Syntax_Syntax.extend_app t1 ((a), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env_arg stack1 t2))
end))
end);
)
end
| (App (env1, head1, aq, r))::stack' when (should_reify cfg stack) -> begin
(

let t0 = t1
in (

let fallback = (fun msg uu____23862 -> ((log cfg (fun uu____23866 -> (

let uu____23867 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not reifying%s: %s\n" msg uu____23867))));
(

let t2 = (FStar_Syntax_Syntax.extend_app head1 ((t1), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env1 stack' t2));
))
in (

let uu____23871 = (

let uu____23872 = (FStar_Syntax_Subst.compress t1)
in uu____23872.FStar_Syntax_Syntax.n)
in (match (uu____23871) with
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_monadic (m, ty)) -> begin
(do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty)
end
| FStar_Syntax_Syntax.Tm_meta (t2, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, ty)) -> begin
(

let lifted = (

let uu____23899 = (closure_as_term cfg env1 ty)
in (reify_lift cfg t2 msrc mtgt uu____23899))
in ((log cfg (fun uu____23903 -> (

let uu____23904 = (FStar_Syntax_Print.term_to_string lifted)
in (FStar_Util.print1 "Reified lift to (1): %s\n" uu____23904))));
(

let uu____23905 = (FStar_List.tl stack)
in (norm cfg env1 uu____23905 lifted));
))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____23906)); FStar_Syntax_Syntax.pos = uu____23907; FStar_Syntax_Syntax.vars = uu____23908}, ((e, uu____23910))::[]) -> begin
(norm cfg env1 stack' e)
end
| FStar_Syntax_Syntax.Tm_app (uu____23939) when cfg.steps.primops -> begin
(

let uu____23954 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____23954) with
| (hd1, args) -> begin
(

let uu____23991 = (

let uu____23992 = (FStar_Syntax_Util.un_uinst hd1)
in uu____23992.FStar_Syntax_Syntax.n)
in (match (uu____23991) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____23996 = (find_prim_step cfg fv)
in (match (uu____23996) with
| FStar_Pervasives_Native.Some ({name = uu____23999; arity = uu____24000; auto_reflect = FStar_Pervasives_Native.Some (n1); strong_reduction_ok = uu____24002; requires_binder_substitution = uu____24003; interpretation = uu____24004}) when (Prims.op_Equality (FStar_List.length args) n1) -> begin
(norm cfg env1 stack' t1)
end
| uu____24019 -> begin
(fallback " (3)" ())
end))
end
| uu____24022 -> begin
(fallback " (4)" ())
end))
end))
end
| uu____24023 -> begin
(fallback " (2)" ())
end))))
end
| (App (env1, head1, aq, r))::stack1 -> begin
(

let t2 = (FStar_Syntax_Syntax.extend_app head1 ((t1), (aq)) FStar_Pervasives_Native.None r)
in (rebuild cfg env1 stack1 t2))
end
| (Match (env', branches, cfg1, r))::stack1 -> begin
((log cfg1 (fun uu____24044 -> (

let uu____24045 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" uu____24045))));
(

let scrutinee_env = env
in (

let env1 = env'
in (

let scrutinee = t1
in (

let norm_and_rebuild_match = (fun uu____24054 -> ((log cfg1 (fun uu____24059 -> (

let uu____24060 = (FStar_Syntax_Print.term_to_string scrutinee)
in (

let uu____24061 = (

let uu____24062 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____24079 -> (match (uu____24079) with
| (p, uu____24089, uu____24090) -> begin
(FStar_Syntax_Print.pat_to_string p)
end))))
in (FStar_All.pipe_right uu____24062 (FStar_String.concat "\n\t")))
in (FStar_Util.print2 "match is irreducible: scrutinee=%s\nbranches=%s\n" uu____24060 uu____24061)))));
(

let whnf = (cfg1.steps.weak || cfg1.steps.hnf)
in (

let cfg_exclude_zeta = (

let new_delta = (FStar_All.pipe_right cfg1.delta_level (FStar_List.filter (fun uu___94_24107 -> (match (uu___94_24107) with
| FStar_TypeChecker_Env.Inlining -> begin
true
end
| FStar_TypeChecker_Env.Eager_unfolding_only -> begin
true
end
| uu____24108 -> begin
false
end))))
in (

let steps = (

let uu___186_24110 = cfg1.steps
in {beta = uu___186_24110.beta; iota = uu___186_24110.iota; zeta = false; weak = uu___186_24110.weak; hnf = uu___186_24110.hnf; primops = uu___186_24110.primops; do_not_unfold_pure_lets = uu___186_24110.do_not_unfold_pure_lets; unfold_until = FStar_Pervasives_Native.None; unfold_only = FStar_Pervasives_Native.None; unfold_fully = uu___186_24110.unfold_fully; unfold_attr = FStar_Pervasives_Native.None; unfold_tac = false; pure_subterms_within_computations = uu___186_24110.pure_subterms_within_computations; simplify = uu___186_24110.simplify; erase_universes = uu___186_24110.erase_universes; allow_unbound_universes = uu___186_24110.allow_unbound_universes; reify_ = uu___186_24110.reify_; compress_uvars = uu___186_24110.compress_uvars; no_full_norm = uu___186_24110.no_full_norm; check_no_uvars = uu___186_24110.check_no_uvars; unmeta = uu___186_24110.unmeta; unascribe = uu___186_24110.unascribe; in_full_norm_request = uu___186_24110.in_full_norm_request; weakly_reduce_scrutinee = uu___186_24110.weakly_reduce_scrutinee})
in (

let uu___187_24115 = cfg1
in {steps = steps; tcenv = uu___187_24115.tcenv; debug = uu___187_24115.debug; delta_level = new_delta; primitive_steps = uu___187_24115.primitive_steps; strong = true; memoize_lazy = uu___187_24115.memoize_lazy; normalize_pure_lets = uu___187_24115.normalize_pure_lets})))
in (

let norm_or_whnf = (fun env2 t2 -> (match (whnf) with
| true -> begin
(closure_as_term cfg_exclude_zeta env2 t2)
end
| uu____24127 -> begin
(norm cfg_exclude_zeta env2 [] t2)
end))
in (

let rec norm_pat = (fun env2 p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____24155) -> begin
((p), (env2))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____24176 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____24236 uu____24237 -> (match (((uu____24236), (uu____24237))) with
| ((pats1, env3), (p1, b)) -> begin
(

let uu____24328 = (norm_pat env3 p1)
in (match (uu____24328) with
| (p2, env4) -> begin
(((((p2), (b)))::pats1), (env4))
end))
end)) (([]), (env2))))
in (match (uu____24176) with
| (pats1, env3) -> begin
(((

let uu___188_24410 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats1)))); FStar_Syntax_Syntax.p = uu___188_24410.FStar_Syntax_Syntax.p})), (env3))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x1 = (

let uu___189_24429 = x
in (

let uu____24430 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___189_24429.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___189_24429.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____24430}))
in (((

let uu___190_24444 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x1); FStar_Syntax_Syntax.p = uu___190_24444.FStar_Syntax_Syntax.p})), ((dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x1 = (

let uu___191_24455 = x
in (

let uu____24456 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___191_24455.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___191_24455.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____24456}))
in (((

let uu___192_24470 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x1); FStar_Syntax_Syntax.p = uu___192_24470.FStar_Syntax_Syntax.p})), ((dummy)::env2)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t2) -> begin
(

let x1 = (

let uu___193_24486 = x
in (

let uu____24487 = (norm_or_whnf env2 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___193_24486.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___193_24486.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____24487}))
in (

let t3 = (norm_or_whnf env2 t2)
in (((

let uu___194_24494 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x1), (t3))); FStar_Syntax_Syntax.p = uu___194_24494.FStar_Syntax_Syntax.p})), (env2))))
end))
in (

let branches1 = (match (env1) with
| [] when whnf -> begin
branches
end
| uu____24504 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch1 -> (

let uu____24518 = (FStar_Syntax_Subst.open_branch branch1)
in (match (uu____24518) with
| (p, wopt, e) -> begin
(

let uu____24538 = (norm_pat env1 p)
in (match (uu____24538) with
| (p1, env2) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____24563 = (norm_or_whnf env2 w)
in FStar_Pervasives_Native.Some (uu____24563))
end)
in (

let e1 = (norm_or_whnf env2 e)
in (FStar_Syntax_Util.branch ((p1), (wopt1), (e1)))))
end))
end)))))
end)
in (

let scrutinee1 = (

let uu____24570 = ((((cfg1.steps.iota && (not (cfg1.steps.weak))) && (not (cfg1.steps.compress_uvars))) && cfg1.steps.weakly_reduce_scrutinee) && (maybe_weakly_reduced scrutinee))
in (match (uu____24570) with
| true -> begin
(norm (

let uu___195_24573 = cfg1
in {steps = (

let uu___196_24576 = cfg1.steps
in {beta = uu___196_24576.beta; iota = uu___196_24576.iota; zeta = uu___196_24576.zeta; weak = uu___196_24576.weak; hnf = uu___196_24576.hnf; primops = uu___196_24576.primops; do_not_unfold_pure_lets = uu___196_24576.do_not_unfold_pure_lets; unfold_until = uu___196_24576.unfold_until; unfold_only = uu___196_24576.unfold_only; unfold_fully = uu___196_24576.unfold_fully; unfold_attr = uu___196_24576.unfold_attr; unfold_tac = uu___196_24576.unfold_tac; pure_subterms_within_computations = uu___196_24576.pure_subterms_within_computations; simplify = uu___196_24576.simplify; erase_universes = uu___196_24576.erase_universes; allow_unbound_universes = uu___196_24576.allow_unbound_universes; reify_ = uu___196_24576.reify_; compress_uvars = uu___196_24576.compress_uvars; no_full_norm = uu___196_24576.no_full_norm; check_no_uvars = uu___196_24576.check_no_uvars; unmeta = uu___196_24576.unmeta; unascribe = uu___196_24576.unascribe; in_full_norm_request = uu___196_24576.in_full_norm_request; weakly_reduce_scrutinee = false}); tcenv = uu___195_24573.tcenv; debug = uu___195_24573.debug; delta_level = uu___195_24573.delta_level; primitive_steps = uu___195_24573.primitive_steps; strong = uu___195_24573.strong; memoize_lazy = uu___195_24573.memoize_lazy; normalize_pure_lets = uu___195_24573.normalize_pure_lets}) scrutinee_env [] scrutinee)
end
| uu____24577 -> begin
scrutinee
end))
in (

let uu____24578 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee1), (branches1)))) r)
in (rebuild cfg1 env1 stack1 uu____24578))))))));
))
in (

let rec is_cons = (fun head1 -> (

let uu____24585 = (

let uu____24586 = (FStar_Syntax_Subst.compress head1)
in uu____24586.FStar_Syntax_Syntax.n)
in (match (uu____24585) with
| FStar_Syntax_Syntax.Tm_uinst (h, uu____24590) -> begin
(is_cons h)
end
| FStar_Syntax_Syntax.Tm_constant (uu____24595) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____24596; FStar_Syntax_Syntax.fv_delta = uu____24597; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)}) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = uu____24598; FStar_Syntax_Syntax.fv_delta = uu____24599; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (uu____24600))}) -> begin
true
end
| uu____24607 -> begin
false
end)))
in (

let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| FStar_Pervasives_Native.None -> begin
b
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let then_branch = b
in (

let else_branch = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (rest)))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (

let rec matches_pat = (fun scrutinee_orig p -> (

let scrutinee1 = (FStar_Syntax_Util.unmeta scrutinee_orig)
in (

let uu____24768 = (FStar_Syntax_Util.head_and_args scrutinee1)
in (match (uu____24768) with
| (head1, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
FStar_Util.Inl ((((bv), (scrutinee_orig)))::[])
end
| FStar_Syntax_Syntax.Pat_wild (bv) -> begin
FStar_Util.Inl ((((bv), (scrutinee_orig)))::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____24855) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (FStar_Const.eq_const s s') -> begin
FStar_Util.Inl ([])
end
| uu____24894 -> begin
(

let uu____24895 = (

let uu____24896 = (is_cons head1)
in (not (uu____24896)))
in FStar_Util.Inr (uu____24895))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let uu____24921 = (

let uu____24922 = (FStar_Syntax_Util.un_uinst head1)
in uu____24922.FStar_Syntax_Syntax.n)
in (match (uu____24921) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| uu____24940 -> begin
(

let uu____24941 = (

let uu____24942 = (is_cons head1)
in (not (uu____24942)))
in FStar_Util.Inr (uu____24941))
end))
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t2, uu____25011))::rest_a, ((p1, uu____25014))::rest_p) -> begin
(

let uu____25058 = (matches_pat t2 p1)
in (match (uu____25058) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end))
end
| uu____25107 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun scrutinee1 p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p1, wopt, b))::rest -> begin
(

let uu____25217 = (matches_pat scrutinee1 p1)
in (match (uu____25217) with
| FStar_Util.Inr (false) -> begin
(matches scrutinee1 rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
((log cfg1 (fun uu____25257 -> (

let uu____25258 = (FStar_Syntax_Print.pat_to_string p1)
in (

let uu____25259 = (

let uu____25260 = (FStar_List.map (fun uu____25270 -> (match (uu____25270) with
| (uu____25275, t2) -> begin
(FStar_Syntax_Print.term_to_string t2)
end)) s)
in (FStar_All.pipe_right uu____25260 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" uu____25258 uu____25259)))));
(

let env0 = env1
in (

let env2 = (FStar_List.fold_left (fun env2 uu____25307 -> (match (uu____25307) with
| (bv, t2) -> begin
(

let uu____25330 = (

let uu____25337 = (

let uu____25340 = (FStar_Syntax_Syntax.mk_binder bv)
in FStar_Pervasives_Native.Some (uu____25340))
in (

let uu____25341 = (

let uu____25342 = (

let uu____25373 = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some ((([]), (t2)))))
in (([]), (t2), (uu____25373), (false)))
in Clos (uu____25342))
in ((uu____25337), (uu____25341))))
in (uu____25330)::env2)
end)) env1 s)
in (

let uu____25538 = (guard_when_clause wopt b rest)
in (norm cfg1 env2 stack1 uu____25538))));
)
end))
end))
in (match (cfg1.steps.iota) with
| true -> begin
(matches scrutinee branches)
end
| uu____25539 -> begin
(norm_and_rebuild_match ())
end)))))))));
)
end));
))


let plugins : ((primitive_step  ->  unit) * (unit  ->  primitive_step Prims.list)) = (

let plugins = (FStar_Util.mk_ref [])
in (

let register = (fun p -> (

let uu____25565 = (

let uu____25568 = (FStar_ST.op_Bang plugins)
in (p)::uu____25568)
in (FStar_ST.op_Colon_Equals plugins uu____25565)))
in (

let retrieve = (fun uu____25784 -> (FStar_ST.op_Bang plugins))
in ((register), (retrieve)))))


let register_plugin : primitive_step  ->  unit = (fun p -> (FStar_Pervasives_Native.fst plugins p))


let retrieve_plugins : unit  ->  primitive_step Prims.list = (fun uu____25915 -> (FStar_Pervasives_Native.snd plugins ()))


let config' : primitive_step Prims.list  ->  step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun psteps s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun uu___95_25956 -> (match (uu___95_25956) with
| UnfoldUntil (k) -> begin
(FStar_TypeChecker_Env.Unfold (k))::[]
end
| Eager_unfolding -> begin
(FStar_TypeChecker_Env.Eager_unfolding_only)::[]
end
| Inlining -> begin
(FStar_TypeChecker_Env.Inlining)::[]
end
| UnfoldTac -> begin
(FStar_TypeChecker_Env.UnfoldTac)::[]
end
| uu____25960 -> begin
[]
end))))
in (

let d1 = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| uu____25966 -> begin
d
end)
in (

let uu____25969 = (to_fsteps s)
in (

let uu____25970 = (

let uu____25971 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("Norm")))
in (

let uu____25972 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("Primops")))
in (

let uu____25973 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("380")))
in (

let uu____25974 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("WPE")))
in (

let uu____25975 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("NormDelayed")))
in (

let uu____25976 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("print_normalized_terms")))
in {gen = uu____25971; primop = uu____25972; b380 = uu____25973; wpe = uu____25974; norm_delayed = uu____25975; print_normalized = uu____25976}))))))
in (

let uu____25977 = (

let uu____25980 = (

let uu____25983 = (retrieve_plugins ())
in (FStar_List.append uu____25983 psteps))
in (add_steps built_in_primitive_steps uu____25980))
in (

let uu____25986 = ((FStar_Options.normalize_pure_terms_for_extraction ()) || (

let uu____25988 = (FStar_All.pipe_right s (FStar_List.contains PureSubtermsWithinComputations))
in (not (uu____25988))))
in {steps = uu____25969; tcenv = e; debug = uu____25970; delta_level = d1; primitive_steps = uu____25977; strong = false; memoize_lazy = true; normalize_pure_lets = uu____25986})))))))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (config' [] s e))


let normalize_with_primitive_steps : primitive_step Prims.list  ->  step Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun ps s e t -> (

let c = (config' ps s e)
in (norm c [] [] t)))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (normalize_with_primitive_steps [] s e t))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (

let uu____26070 = (config s e)
in (norm_comp uu____26070 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let uu____26087 = (config [] env)
in (norm_universe uu____26087 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (

let cfg = (config ((UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::(EraseUniverses)::[]) env)
in (

let non_info = (fun t -> (

let uu____26111 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative uu____26111)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____26118) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let uu___197_26137 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.pos = uu___197_26137.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___197_26137.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in (

let uu____26144 = ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ))
in (match (uu____26144) with
| true -> begin
(

let ct1 = (

let uu____26146 = (downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)
in (match (uu____26146) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(

let flags1 = (

let uu____26153 = (FStar_Ident.lid_equals pure_eff FStar_Parser_Const.effect_Tot_lid)
in (match (uu____26153) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::ct.FStar_Syntax_Syntax.flags
end
| uu____26156 -> begin
ct.FStar_Syntax_Syntax.flags
end))
in (

let uu___198_26157 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___198_26157.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = uu___198_26157.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___198_26157.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = flags1}))
end
| FStar_Pervasives_Native.None -> begin
(

let ct1 = (FStar_TypeChecker_Env.unfold_effect_abbrev cfg.tcenv c)
in (

let uu___199_26159 = ct1
in {FStar_Syntax_Syntax.comp_univs = uu___199_26159.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu___199_26159.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___199_26159.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___199_26159.FStar_Syntax_Syntax.flags}))
end))
in (

let uu___200_26160 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct1); FStar_Syntax_Syntax.pos = uu___200_26160.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___200_26160.FStar_Syntax_Syntax.vars}))
end
| uu____26161 -> begin
c
end)))
end
| uu____26162 -> begin
c
end))))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (

let uu____26180 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative uu____26180)))
in (

let uu____26187 = ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ))
in (match (uu____26187) with
| true -> begin
(

let uu____26188 = (downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)
in (match (uu____26188) with
| FStar_Pervasives_Native.Some (pure_eff) -> begin
(FStar_Syntax_Syntax.mk_lcomp pure_eff lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags (fun uu____26194 -> (

let uu____26195 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (ghost_to_pure env uu____26195))))
end
| FStar_Pervasives_Native.None -> begin
lc
end))
end
| uu____26196 -> begin
lc
end)))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (

let t1 = (FStar_All.try_with (fun uu___202_26209 -> (match (()) with
| () -> begin
(normalize ((AllowUnboundUniverses)::[]) env t)
end)) (fun uu___201_26213 -> (match (uu___201_26213) with
| e -> begin
((

let uu____26216 = (

let uu____26221 = (

let uu____26222 = (FStar_Util.message_of_exn e)
in (FStar_Util.format1 "Normalization failed with error %s\n" uu____26222))
in ((FStar_Errors.Warning_NormalizationFailure), (uu____26221)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____26216));
t;
)
end)))
in (FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let c1 = (FStar_All.try_with (fun uu___204_26236 -> (match (()) with
| () -> begin
(

let uu____26237 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp uu____26237 [] c))
end)) (fun uu___203_26247 -> (match (uu___203_26247) with
| e -> begin
((

let uu____26250 = (

let uu____26255 = (

let uu____26256 = (FStar_Util.message_of_exn e)
in (FStar_Util.format1 "Normalization failed with error %s\n" uu____26256))
in ((FStar_Errors.Warning_NormalizationFailure), (uu____26255)))
in (FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____26250));
c;
)
end)))
in (FStar_Syntax_Print.comp_to_string' env.FStar_TypeChecker_Env.dsenv c1)))


let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (

let t = (normalize (FStar_List.append steps ((Beta)::[])) env t0)
in (

let rec aux = (fun t1 -> (

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let t01 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t01.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(

let uu____26301 = (

let uu____26302 = (

let uu____26309 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (uu____26309)))
in FStar_Syntax_Syntax.Tm_refine (uu____26302))
in (mk uu____26301 t01.FStar_Syntax_Syntax.pos))
end
| uu____26314 -> begin
t2
end))
end
| uu____26315 -> begin
t2
end)))
in (aux t))))


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (normalize ((Primops)::(Weak)::(HNF)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Beta)::[]) env t))


let reduce_or_remove_uvar_solutions : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun remove env t -> (normalize (FStar_List.append (match (remove) with
| true -> begin
(CheckNoUvars)::[]
end
| uu____26343 -> begin
[]
end) ((Beta)::(DoNotUnfoldPureLets)::(CompressUvars)::(Exclude (Zeta))::(Exclude (Iota))::(NoFullNorm)::[])) env t))


let reduce_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions false env t))


let remove_uvar_solutions : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (reduce_or_remove_uvar_solutions true env t))


let eta_expand_with_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e t_e -> (

let uu____26379 = (FStar_Syntax_Util.arrow_formals_comp t_e)
in (match (uu____26379) with
| (formals, c) -> begin
(match (formals) with
| [] -> begin
e
end
| uu____26408 -> begin
(

let uu____26415 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____26415) with
| (actuals, uu____26425, uu____26426) -> begin
(match ((Prims.op_Equality (FStar_List.length actuals) (FStar_List.length formals))) with
| true -> begin
e
end
| uu____26439 -> begin
(

let uu____26440 = (FStar_All.pipe_right formals FStar_Syntax_Util.args_of_binders)
in (match (uu____26440) with
| (binders, args) -> begin
(

let uu____26457 = (FStar_Syntax_Syntax.mk_Tm_app e args FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Util.abs binders uu____26457 (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp c)))))
end))
end)
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(eta_expand_with_type env t x.FStar_Syntax_Syntax.sort)
end
| uu____26469 -> begin
(

let uu____26470 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____26470) with
| (head1, args) -> begin
(

let uu____26507 = (

let uu____26508 = (FStar_Syntax_Subst.compress head1)
in uu____26508.FStar_Syntax_Syntax.n)
in (match (uu____26507) with
| FStar_Syntax_Syntax.Tm_uvar (uu____26511, thead) -> begin
(

let uu____26537 = (FStar_Syntax_Util.arrow_formals thead)
in (match (uu____26537) with
| (formals, tres) -> begin
(match ((Prims.op_Equality (FStar_List.length formals) (FStar_List.length args))) with
| true -> begin
t
end
| uu____26578 -> begin
(

let uu____26579 = (env.FStar_TypeChecker_Env.type_of (

let uu___205_26587 = env
in {FStar_TypeChecker_Env.solver = uu___205_26587.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___205_26587.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___205_26587.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___205_26587.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___205_26587.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___205_26587.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___205_26587.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___205_26587.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___205_26587.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___205_26587.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___205_26587.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___205_26587.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___205_26587.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___205_26587.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___205_26587.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___205_26587.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___205_26587.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___205_26587.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___205_26587.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___205_26587.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___205_26587.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___205_26587.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___205_26587.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___205_26587.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___205_26587.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___205_26587.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___205_26587.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___205_26587.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___205_26587.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___205_26587.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___205_26587.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___205_26587.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___205_26587.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___205_26587.FStar_TypeChecker_Env.dep_graph}) t)
in (match (uu____26579) with
| (uu____26588, ty, uu____26590) -> begin
(eta_expand_with_type env t ty)
end))
end)
end))
end
| uu____26591 -> begin
(

let uu____26592 = (env.FStar_TypeChecker_Env.type_of (

let uu___206_26600 = env
in {FStar_TypeChecker_Env.solver = uu___206_26600.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___206_26600.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___206_26600.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___206_26600.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___206_26600.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___206_26600.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = FStar_Pervasives_Native.None; FStar_TypeChecker_Env.sigtab = uu___206_26600.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___206_26600.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___206_26600.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___206_26600.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___206_26600.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___206_26600.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___206_26600.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___206_26600.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___206_26600.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___206_26600.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___206_26600.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___206_26600.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___206_26600.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___206_26600.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___206_26600.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___206_26600.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___206_26600.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___206_26600.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qtbl_name_and_index = uu___206_26600.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___206_26600.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___206_26600.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___206_26600.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___206_26600.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___206_26600.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___206_26600.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___206_26600.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___206_26600.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___206_26600.FStar_TypeChecker_Env.dep_graph}) t)
in (match (uu____26592) with
| (uu____26601, ty, uu____26603) -> begin
(eta_expand_with_type env t ty)
end))
end))
end))
end))


let rec elim_delayed_subst_term : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let t1 = (FStar_Syntax_Subst.compress t)
in (

let elim_bv = (fun x -> (

let uu___207_26676 = x
in (

let uu____26677 = (elim_delayed_subst_term x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___207_26676.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___207_26676.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____26677})))
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____26680) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_bvar (uu____26705) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_name (uu____26706) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_fvar (uu____26707) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_uinst (uu____26708) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_constant (uu____26715) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_type (uu____26716) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_lazy (uu____26717) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
t1
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, rc_opt) -> begin
(

let elim_rc = (fun rc -> (

let uu___208_26747 = rc
in (

let uu____26748 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ elim_delayed_subst_term)
in (

let uu____26755 = (elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags)
in {FStar_Syntax_Syntax.residual_effect = uu___208_26747.FStar_Syntax_Syntax.residual_effect; FStar_Syntax_Syntax.residual_typ = uu____26748; FStar_Syntax_Syntax.residual_flags = uu____26755}))))
in (

let uu____26758 = (

let uu____26759 = (

let uu____26776 = (elim_delayed_subst_binders bs)
in (

let uu____26783 = (elim_delayed_subst_term t2)
in (

let uu____26784 = (FStar_Util.map_opt rc_opt elim_rc)
in ((uu____26776), (uu____26783), (uu____26784)))))
in FStar_Syntax_Syntax.Tm_abs (uu____26759))
in (mk1 uu____26758)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____26813 = (

let uu____26814 = (

let uu____26827 = (elim_delayed_subst_binders bs)
in (

let uu____26834 = (elim_delayed_subst_comp c)
in ((uu____26827), (uu____26834))))
in FStar_Syntax_Syntax.Tm_arrow (uu____26814))
in (mk1 uu____26813))
end
| FStar_Syntax_Syntax.Tm_refine (bv, phi) -> begin
(

let uu____26847 = (

let uu____26848 = (

let uu____26855 = (elim_bv bv)
in (

let uu____26856 = (elim_delayed_subst_term phi)
in ((uu____26855), (uu____26856))))
in FStar_Syntax_Syntax.Tm_refine (uu____26848))
in (mk1 uu____26847))
end
| FStar_Syntax_Syntax.Tm_app (t2, args) -> begin
(

let uu____26879 = (

let uu____26880 = (

let uu____26895 = (elim_delayed_subst_term t2)
in (

let uu____26896 = (elim_delayed_subst_args args)
in ((uu____26895), (uu____26896))))
in FStar_Syntax_Syntax.Tm_app (uu____26880))
in (mk1 uu____26879))
end
| FStar_Syntax_Syntax.Tm_match (t2, branches) -> begin
(

let rec elim_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu___209_26962 = p
in (

let uu____26963 = (

let uu____26964 = (elim_bv x)
in FStar_Syntax_Syntax.Pat_var (uu____26964))
in {FStar_Syntax_Syntax.v = uu____26963; FStar_Syntax_Syntax.p = uu___209_26962.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu___210_26966 = p
in (

let uu____26967 = (

let uu____26968 = (elim_bv x)
in FStar_Syntax_Syntax.Pat_wild (uu____26968))
in {FStar_Syntax_Syntax.v = uu____26967; FStar_Syntax_Syntax.p = uu___210_26966.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let uu___211_26975 = p
in (

let uu____26976 = (

let uu____26977 = (

let uu____26984 = (elim_bv x)
in (

let uu____26985 = (elim_delayed_subst_term t0)
in ((uu____26984), (uu____26985))))
in FStar_Syntax_Syntax.Pat_dot_term (uu____26977))
in {FStar_Syntax_Syntax.v = uu____26976; FStar_Syntax_Syntax.p = uu___211_26975.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu___212_27004 = p
in (

let uu____27005 = (

let uu____27006 = (

let uu____27019 = (FStar_List.map (fun uu____27042 -> (match (uu____27042) with
| (x, b) -> begin
(

let uu____27055 = (elim_pat x)
in ((uu____27055), (b)))
end)) pats)
in ((fv), (uu____27019)))
in FStar_Syntax_Syntax.Pat_cons (uu____27006))
in {FStar_Syntax_Syntax.v = uu____27005; FStar_Syntax_Syntax.p = uu___212_27004.FStar_Syntax_Syntax.p}))
end
| uu____27068 -> begin
p
end))
in (

let elim_branch = (fun uu____27092 -> (match (uu____27092) with
| (pat, wopt, t3) -> begin
(

let uu____27118 = (elim_pat pat)
in (

let uu____27121 = (FStar_Util.map_opt wopt elim_delayed_subst_term)
in (

let uu____27124 = (elim_delayed_subst_term t3)
in ((uu____27118), (uu____27121), (uu____27124)))))
end))
in (

let uu____27129 = (

let uu____27130 = (

let uu____27153 = (elim_delayed_subst_term t2)
in (

let uu____27154 = (FStar_List.map elim_branch branches)
in ((uu____27153), (uu____27154))))
in FStar_Syntax_Syntax.Tm_match (uu____27130))
in (mk1 uu____27129))))
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, a, lopt) -> begin
(

let elim_ascription = (fun uu____27265 -> (match (uu____27265) with
| (tc, topt) -> begin
(

let uu____27300 = (match (tc) with
| FStar_Util.Inl (t3) -> begin
(

let uu____27310 = (elim_delayed_subst_term t3)
in FStar_Util.Inl (uu____27310))
end
| FStar_Util.Inr (c) -> begin
(

let uu____27312 = (elim_delayed_subst_comp c)
in FStar_Util.Inr (uu____27312))
end)
in (

let uu____27313 = (FStar_Util.map_opt topt elim_delayed_subst_term)
in ((uu____27300), (uu____27313))))
end))
in (

let uu____27322 = (

let uu____27323 = (

let uu____27350 = (elim_delayed_subst_term t2)
in (

let uu____27351 = (elim_ascription a)
in ((uu____27350), (uu____27351), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (uu____27323))
in (mk1 uu____27322)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t2) -> begin
(

let elim_lb = (fun lb -> (

let uu___213_27398 = lb
in (

let uu____27399 = (elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____27402 = (elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___213_27398.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___213_27398.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____27399; FStar_Syntax_Syntax.lbeff = uu___213_27398.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____27402; FStar_Syntax_Syntax.lbattrs = uu___213_27398.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___213_27398.FStar_Syntax_Syntax.lbpos}))))
in (

let uu____27405 = (

let uu____27406 = (

let uu____27419 = (

let uu____27426 = (FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs))
in (((FStar_Pervasives_Native.fst lbs)), (uu____27426)))
in (

let uu____27435 = (elim_delayed_subst_term t2)
in ((uu____27419), (uu____27435))))
in FStar_Syntax_Syntax.Tm_let (uu____27406))
in (mk1 uu____27405)))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, t2) -> begin
(

let uu____27468 = (

let uu____27469 = (

let uu____27486 = (elim_delayed_subst_term t2)
in ((uv), (uu____27486)))
in FStar_Syntax_Syntax.Tm_uvar (uu____27469))
in (mk1 uu____27468))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(

let qi1 = (FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi)
in (

let uu____27504 = (

let uu____27505 = (

let uu____27512 = (elim_delayed_subst_term tm)
in ((uu____27512), (qi1)))
in FStar_Syntax_Syntax.Tm_quoted (uu____27505))
in (mk1 uu____27504)))
end
| FStar_Syntax_Syntax.Tm_meta (t2, md) -> begin
(

let uu____27519 = (

let uu____27520 = (

let uu____27527 = (elim_delayed_subst_term t2)
in (

let uu____27528 = (elim_delayed_subst_meta md)
in ((uu____27527), (uu____27528))))
in FStar_Syntax_Syntax.Tm_meta (uu____27520))
in (mk1 uu____27519))
end)))))
and elim_delayed_subst_cflags : FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun flags1 -> (FStar_List.map (fun uu___96_27535 -> (match (uu___96_27535) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(

let uu____27539 = (elim_delayed_subst_term t)
in FStar_Syntax_Syntax.DECREASES (uu____27539))
end
| f -> begin
f
end)) flags1))
and elim_delayed_subst_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun c -> (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____27562 = (

let uu____27563 = (

let uu____27572 = (elim_delayed_subst_term t)
in ((uu____27572), (uopt)))
in FStar_Syntax_Syntax.Total (uu____27563))
in (mk1 uu____27562))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____27585 = (

let uu____27586 = (

let uu____27595 = (elim_delayed_subst_term t)
in ((uu____27595), (uopt)))
in FStar_Syntax_Syntax.GTotal (uu____27586))
in (mk1 uu____27585))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let ct1 = (

let uu___214_27600 = ct
in (

let uu____27601 = (elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ)
in (

let uu____27604 = (elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args)
in (

let uu____27613 = (elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.comp_univs = uu___214_27600.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___214_27600.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu____27601; FStar_Syntax_Syntax.effect_args = uu____27604; FStar_Syntax_Syntax.flags = uu____27613}))))
in (mk1 (FStar_Syntax_Syntax.Comp (ct1))))
end)))
and elim_delayed_subst_meta : FStar_Syntax_Syntax.metadata  ->  FStar_Syntax_Syntax.metadata = (fun uu___97_27616 -> (match (uu___97_27616) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let uu____27628 = (FStar_List.map elim_delayed_subst_args args)
in FStar_Syntax_Syntax.Meta_pattern (uu____27628))
end
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let uu____27661 = (

let uu____27668 = (elim_delayed_subst_term t)
in ((m), (uu____27668)))
in FStar_Syntax_Syntax.Meta_monadic (uu____27661))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t) -> begin
(

let uu____27676 = (

let uu____27685 = (elim_delayed_subst_term t)
in ((m1), (m2), (uu____27685)))
in FStar_Syntax_Syntax.Meta_monadic_lift (uu____27676))
end
| m -> begin
m
end))
and elim_delayed_subst_args : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list = (fun args -> (FStar_List.map (fun uu____27708 -> (match (uu____27708) with
| (t, q) -> begin
(

let uu____27719 = (elim_delayed_subst_term t)
in ((uu____27719), (q)))
end)) args))
and elim_delayed_subst_binders : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun bs -> (FStar_List.map (fun uu____27739 -> (match (uu____27739) with
| (x, q) -> begin
(

let uu____27750 = (

let uu___215_27751 = x
in (

let uu____27752 = (elim_delayed_subst_term x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___215_27751.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___215_27751.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____27752}))
in ((uu____27750), (q)))
end)) bs))


let elim_uvars_aux_tc : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.comp) FStar_Util.either  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) FStar_Util.either) = (fun env univ_names binders tc -> (

let t = (match (((binders), (tc))) with
| ([], FStar_Util.Inl (t)) -> begin
t
end
| ([], FStar_Util.Inr (c)) -> begin
(failwith "Impossible: empty bindes with a comp")
end
| (uu____27836, FStar_Util.Inr (c)) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (c)))) FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos)
end
| (uu____27842, FStar_Util.Inl (t)) -> begin
(

let uu____27848 = (

let uu____27855 = (

let uu____27856 = (

let uu____27869 = (FStar_Syntax_Syntax.mk_Total t)
in ((binders), (uu____27869)))
in FStar_Syntax_Syntax.Tm_arrow (uu____27856))
in (FStar_Syntax_Syntax.mk uu____27855))
in (uu____27848 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
end)
in (

let uu____27873 = (FStar_Syntax_Subst.open_univ_vars univ_names t)
in (match (uu____27873) with
| (univ_names1, t1) -> begin
(

let t2 = (remove_uvar_solutions env t1)
in (

let t3 = (FStar_Syntax_Subst.close_univ_vars univ_names1 t2)
in (

let t4 = (elim_delayed_subst_term t3)
in (

let uu____27901 = (match (binders) with
| [] -> begin
(([]), (FStar_Util.Inl (t4)))
end
| uu____27956 -> begin
(

let uu____27957 = (

let uu____27966 = (

let uu____27967 = (FStar_Syntax_Subst.compress t4)
in uu____27967.FStar_Syntax_Syntax.n)
in ((uu____27966), (tc)))
in (match (uu____27957) with
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inr (uu____27992)) -> begin
((binders1), (FStar_Util.Inr (c)))
end
| (FStar_Syntax_Syntax.Tm_arrow (binders1, c), FStar_Util.Inl (uu____28029)) -> begin
((binders1), (FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))))
end
| (uu____28068, FStar_Util.Inl (uu____28069)) -> begin
(([]), (FStar_Util.Inl (t4)))
end
| uu____28092 -> begin
(failwith "Impossible")
end))
end)
in (match (uu____27901) with
| (binders1, tc1) -> begin
((univ_names1), (binders1), (tc1))
end)))))
end))))


let elim_uvars_aux_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.term) = (fun env univ_names binders t -> (

let uu____28205 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl (t)))
in (match (uu____28205) with
| (univ_names1, binders1, tc) -> begin
(

let uu____28263 = (FStar_Util.left tc)
in ((univ_names1), (binders1), (uu____28263)))
end)))


let elim_uvars_aux_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) = (fun env univ_names binders c -> (

let uu____28306 = (elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr (c)))
in (match (uu____28306) with
| (univ_names1, binders1, tc) -> begin
(

let uu____28366 = (FStar_Util.right tc)
in ((univ_names1), (binders1), (uu____28366)))
end)))


let rec elim_uvars : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun env s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univ_names, binders, typ, lids, lids') -> begin
(

let uu____28403 = (elim_uvars_aux_t env univ_names binders typ)
in (match (uu____28403) with
| (univ_names1, binders1, typ1) -> begin
(

let uu___216_28431 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lid), (univ_names1), (binders1), (typ1), (lids), (lids'))); FStar_Syntax_Syntax.sigrng = uu___216_28431.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___216_28431.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___216_28431.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___216_28431.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_bundle (sigs, lids) -> begin
(

let uu___217_28452 = s
in (

let uu____28453 = (

let uu____28454 = (

let uu____28463 = (FStar_List.map (elim_uvars env) sigs)
in ((uu____28463), (lids)))
in FStar_Syntax_Syntax.Sig_bundle (uu____28454))
in {FStar_Syntax_Syntax.sigel = uu____28453; FStar_Syntax_Syntax.sigrng = uu___217_28452.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___217_28452.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___217_28452.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___217_28452.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univ_names, typ, lident, i, lids) -> begin
(

let uu____28480 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____28480) with
| (univ_names1, uu____28498, typ1) -> begin
(

let uu___218_28512 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lid), (univ_names1), (typ1), (lident), (i), (lids))); FStar_Syntax_Syntax.sigrng = uu___218_28512.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___218_28512.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___218_28512.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___218_28512.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univ_names, typ) -> begin
(

let uu____28518 = (elim_uvars_aux_t env univ_names [] typ)
in (match (uu____28518) with
| (univ_names1, uu____28536, typ1) -> begin
(

let uu___219_28550 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (univ_names1), (typ1))); FStar_Syntax_Syntax.sigrng = uu___219_28550.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___219_28550.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___219_28550.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___219_28550.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) -> begin
(

let lbs1 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu____28584 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____28584) with
| (opening, lbunivs) -> begin
(

let elim = (fun t -> (

let uu____28609 = (

let uu____28610 = (

let uu____28611 = (FStar_Syntax_Subst.subst opening t)
in (remove_uvar_solutions env uu____28611))
in (FStar_Syntax_Subst.close_univ_vars lbunivs uu____28610))
in (elim_delayed_subst_term uu____28609)))
in (

let lbtyp = (elim lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbdef = (elim lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___220_28614 = lb
in {FStar_Syntax_Syntax.lbname = uu___220_28614.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = lbunivs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = uu___220_28614.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___220_28614.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___220_28614.FStar_Syntax_Syntax.lbpos}))))
end)))))
in (

let uu___221_28615 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((b), (lbs1))), (lids))); FStar_Syntax_Syntax.sigrng = uu___221_28615.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___221_28615.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___221_28615.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___221_28615.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_main (t) -> begin
(

let uu___222_28627 = s
in (

let uu____28628 = (

let uu____28629 = (remove_uvar_solutions env t)
in FStar_Syntax_Syntax.Sig_main (uu____28629))
in {FStar_Syntax_Syntax.sigel = uu____28628; FStar_Syntax_Syntax.sigrng = uu___222_28627.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___222_28627.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___222_28627.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___222_28627.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, t) -> begin
(

let uu____28633 = (elim_uvars_aux_t env us [] t)
in (match (uu____28633) with
| (us1, uu____28651, t1) -> begin
(

let uu___223_28665 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((l), (us1), (t1))); FStar_Syntax_Syntax.sigrng = uu___223_28665.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___223_28665.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___223_28665.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___223_28665.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____28666) -> begin
(failwith "Impossible: should have been desugared already")
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____28668 = (elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____28668) with
| (univs1, binders, signature) -> begin
(

let uu____28696 = (

let uu____28705 = (FStar_Syntax_Subst.univ_var_opening univs1)
in (match (uu____28705) with
| (univs_opening, univs2) -> begin
(

let uu____28732 = (FStar_Syntax_Subst.univ_var_closing univs2)
in ((univs_opening), (uu____28732)))
end))
in (match (uu____28696) with
| (univs_opening, univs_closing) -> begin
(

let uu____28749 = (

let binders1 = (FStar_Syntax_Subst.open_binders binders)
in (

let uu____28755 = (FStar_Syntax_Subst.opening_of_binders binders1)
in (

let uu____28756 = (FStar_Syntax_Subst.closing_of_binders binders1)
in ((uu____28755), (uu____28756)))))
in (match (uu____28749) with
| (b_opening, b_closing) -> begin
(

let n1 = (FStar_List.length univs1)
in (

let n_binders = (FStar_List.length binders)
in (

let elim_tscheme = (fun uu____28780 -> (match (uu____28780) with
| (us, t) -> begin
(

let n_us = (FStar_List.length us)
in (

let uu____28798 = (FStar_Syntax_Subst.open_univ_vars us t)
in (match (uu____28798) with
| (us1, t1) -> begin
(

let uu____28809 = (

let uu____28814 = (FStar_All.pipe_right b_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____28821 = (FStar_All.pipe_right b_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____28814), (uu____28821))))
in (match (uu____28809) with
| (b_opening1, b_closing1) -> begin
(

let uu____28834 = (

let uu____28839 = (FStar_All.pipe_right univs_opening (FStar_Syntax_Subst.shift_subst n_us))
in (

let uu____28848 = (FStar_All.pipe_right univs_closing (FStar_Syntax_Subst.shift_subst n_us))
in ((uu____28839), (uu____28848))))
in (match (uu____28834) with
| (univs_opening1, univs_closing1) -> begin
(

let t2 = (

let uu____28864 = (FStar_Syntax_Subst.subst b_opening1 t1)
in (FStar_Syntax_Subst.subst univs_opening1 uu____28864))
in (

let uu____28865 = (elim_uvars_aux_t env [] [] t2)
in (match (uu____28865) with
| (uu____28886, uu____28887, t3) -> begin
(

let t4 = (

let uu____28902 = (

let uu____28903 = (FStar_Syntax_Subst.close_univ_vars us1 t3)
in (FStar_Syntax_Subst.subst b_closing1 uu____28903))
in (FStar_Syntax_Subst.subst univs_closing1 uu____28902))
in ((us1), (t4)))
end)))
end))
end))
end)))
end))
in (

let elim_term = (fun t -> (

let uu____28910 = (elim_uvars_aux_t env univs1 binders t)
in (match (uu____28910) with
| (uu____28923, uu____28924, t1) -> begin
t1
end)))
in (

let elim_action = (fun a -> (

let action_typ_templ = (

let body = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((a.FStar_Syntax_Syntax.action_defn), (((FStar_Util.Inl (a.FStar_Syntax_Syntax.action_typ)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (match (a.FStar_Syntax_Syntax.action_params) with
| [] -> begin
body
end
| uu____28986 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((a.FStar_Syntax_Syntax.action_params), (body), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
end))
in (

let destruct_action_body = (fun body -> (

let uu____29005 = (

let uu____29006 = (FStar_Syntax_Subst.compress body)
in uu____29006.FStar_Syntax_Syntax.n)
in (match (uu____29005) with
| FStar_Syntax_Syntax.Tm_ascribed (defn, (FStar_Util.Inl (typ), FStar_Pervasives_Native.None), FStar_Pervasives_Native.None) -> begin
((defn), (typ))
end
| uu____29065 -> begin
(failwith "Impossible")
end)))
in (

let destruct_action_typ_templ = (fun t -> (

let uu____29096 = (

let uu____29097 = (FStar_Syntax_Subst.compress t)
in uu____29097.FStar_Syntax_Syntax.n)
in (match (uu____29096) with
| FStar_Syntax_Syntax.Tm_abs (pars, body, uu____29118) -> begin
(

let uu____29139 = (destruct_action_body body)
in (match (uu____29139) with
| (defn, typ) -> begin
((pars), (defn), (typ))
end))
end
| uu____29184 -> begin
(

let uu____29185 = (destruct_action_body t)
in (match (uu____29185) with
| (defn, typ) -> begin
(([]), (defn), (typ))
end))
end)))
in (

let uu____29234 = (elim_tscheme ((a.FStar_Syntax_Syntax.action_univs), (action_typ_templ)))
in (match (uu____29234) with
| (action_univs, t) -> begin
(

let uu____29243 = (destruct_action_typ_templ t)
in (match (uu____29243) with
| (action_params, action_defn, action_typ) -> begin
(

let a' = (

let uu___224_29284 = a
in {FStar_Syntax_Syntax.action_name = uu___224_29284.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___224_29284.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action_univs; FStar_Syntax_Syntax.action_params = action_params; FStar_Syntax_Syntax.action_defn = action_defn; FStar_Syntax_Syntax.action_typ = action_typ})
in a')
end))
end))))))
in (

let ed1 = (

let uu___225_29286 = ed
in (

let uu____29287 = (elim_tscheme ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____29288 = (elim_tscheme ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____29289 = (elim_tscheme ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____29290 = (elim_tscheme ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____29291 = (elim_tscheme ed.FStar_Syntax_Syntax.stronger)
in (

let uu____29292 = (elim_tscheme ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____29293 = (elim_tscheme ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____29294 = (elim_tscheme ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____29295 = (elim_tscheme ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____29296 = (elim_tscheme ed.FStar_Syntax_Syntax.trivial)
in (

let uu____29297 = (elim_term ed.FStar_Syntax_Syntax.repr)
in (

let uu____29298 = (elim_tscheme ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____29299 = (elim_tscheme ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____29300 = (FStar_List.map elim_action ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___225_29286.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___225_29286.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu____29287; FStar_Syntax_Syntax.bind_wp = uu____29288; FStar_Syntax_Syntax.if_then_else = uu____29289; FStar_Syntax_Syntax.ite_wp = uu____29290; FStar_Syntax_Syntax.stronger = uu____29291; FStar_Syntax_Syntax.close_wp = uu____29292; FStar_Syntax_Syntax.assert_p = uu____29293; FStar_Syntax_Syntax.assume_p = uu____29294; FStar_Syntax_Syntax.null_wp = uu____29295; FStar_Syntax_Syntax.trivial = uu____29296; FStar_Syntax_Syntax.repr = uu____29297; FStar_Syntax_Syntax.return_repr = uu____29298; FStar_Syntax_Syntax.bind_repr = uu____29299; FStar_Syntax_Syntax.actions = uu____29300; FStar_Syntax_Syntax.eff_attrs = uu___225_29286.FStar_Syntax_Syntax.eff_attrs})))))))))))))))
in (

let uu___226_29303 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ed1); FStar_Syntax_Syntax.sigrng = uu___226_29303.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___226_29303.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___226_29303.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___226_29303.FStar_Syntax_Syntax.sigattrs})))))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub_eff) -> begin
(

let elim_tscheme_opt = (fun uu___98_29322 -> (match (uu___98_29322) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (us, t) -> begin
(

let uu____29349 = (elim_uvars_aux_t env us [] t)
in (match (uu____29349) with
| (us1, uu____29373, t1) -> begin
FStar_Pervasives_Native.Some (((us1), (t1)))
end))
end))
in (

let sub_eff1 = (

let uu___227_29392 = sub_eff
in (

let uu____29393 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp)
in (

let uu____29396 = (elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift)
in {FStar_Syntax_Syntax.source = uu___227_29392.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___227_29392.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = uu____29393; FStar_Syntax_Syntax.lift = uu____29396})))
in (

let uu___228_29399 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub_eff1); FStar_Syntax_Syntax.sigrng = uu___228_29399.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___228_29399.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___228_29399.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___228_29399.FStar_Syntax_Syntax.sigattrs})))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univ_names, binders, comp, flags1) -> begin
(

let uu____29409 = (elim_uvars_aux_c env univ_names binders comp)
in (match (uu____29409) with
| (univ_names1, binders1, comp1) -> begin
(

let uu___229_29443 = s
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (univ_names1), (binders1), (comp1), (flags1))); FStar_Syntax_Syntax.sigrng = uu___229_29443.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___229_29443.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___229_29443.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___229_29443.FStar_Syntax_Syntax.sigattrs})
end))
end
| FStar_Syntax_Syntax.Sig_pragma (uu____29454) -> begin
s
end
| FStar_Syntax_Syntax.Sig_splice (uu____29455) -> begin
s
end))


let erase_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (normalize ((EraseUniverses)::(AllowUnboundUniverses)::[]) env t))




