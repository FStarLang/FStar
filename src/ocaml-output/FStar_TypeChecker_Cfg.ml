
open Prims
open FStar_Pervasives
type fsteps =
{beta : Prims.bool; iota : Prims.bool; zeta : Prims.bool; weak : Prims.bool; hnf : Prims.bool; primops : Prims.bool; do_not_unfold_pure_lets : Prims.bool; unfold_until : FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option; unfold_only : FStar_Ident.lid Prims.list FStar_Pervasives_Native.option; unfold_fully : FStar_Ident.lid Prims.list FStar_Pervasives_Native.option; unfold_attr : FStar_Ident.lid Prims.list FStar_Pervasives_Native.option; unfold_tac : Prims.bool; pure_subterms_within_computations : Prims.bool; simplify : Prims.bool; erase_universes : Prims.bool; allow_unbound_universes : Prims.bool; reify_ : Prims.bool; compress_uvars : Prims.bool; no_full_norm : Prims.bool; check_no_uvars : Prims.bool; unmeta : Prims.bool; unascribe : Prims.bool; in_full_norm_request : Prims.bool; weakly_reduce_scrutinee : Prims.bool; nbe_step : Prims.bool; for_extraction : Prims.bool}


let __proj__Mkfsteps__item__beta : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
beta
end))


let __proj__Mkfsteps__item__iota : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
iota1
end))


let __proj__Mkfsteps__item__zeta : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
zeta1
end))


let __proj__Mkfsteps__item__weak : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
weak1
end))


let __proj__Mkfsteps__item__hnf : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
hnf1
end))


let __proj__Mkfsteps__item__primops : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
primops1
end))


let __proj__Mkfsteps__item__do_not_unfold_pure_lets : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
do_not_unfold_pure_lets
end))


let __proj__Mkfsteps__item__unfold_until : fsteps  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
unfold_until
end))


let __proj__Mkfsteps__item__unfold_only : fsteps  ->  FStar_Ident.lid Prims.list FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
unfold_only
end))


let __proj__Mkfsteps__item__unfold_fully : fsteps  ->  FStar_Ident.lid Prims.list FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
unfold_fully
end))


let __proj__Mkfsteps__item__unfold_attr : fsteps  ->  FStar_Ident.lid Prims.list FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
unfold_attr
end))


let __proj__Mkfsteps__item__unfold_tac : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
unfold_tac
end))


let __proj__Mkfsteps__item__pure_subterms_within_computations : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
pure_subterms_within_computations
end))


let __proj__Mkfsteps__item__simplify : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
simplify1
end))


let __proj__Mkfsteps__item__erase_universes : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
erase_universes
end))


let __proj__Mkfsteps__item__allow_unbound_universes : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
allow_unbound_universes
end))


let __proj__Mkfsteps__item__reify_ : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
reify_1
end))


let __proj__Mkfsteps__item__compress_uvars : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
compress_uvars
end))


let __proj__Mkfsteps__item__no_full_norm : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
no_full_norm
end))


let __proj__Mkfsteps__item__check_no_uvars : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
check_no_uvars
end))


let __proj__Mkfsteps__item__unmeta : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
unmeta1
end))


let __proj__Mkfsteps__item__unascribe : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
unascribe1
end))


let __proj__Mkfsteps__item__in_full_norm_request : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
in_full_norm_request
end))


let __proj__Mkfsteps__item__weakly_reduce_scrutinee : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
weakly_reduce_scrutinee
end))


let __proj__Mkfsteps__item__nbe_step : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
nbe_step
end))


let __proj__Mkfsteps__item__for_extraction : fsteps  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {beta = beta; iota = iota1; zeta = zeta1; weak = weak1; hnf = hnf1; primops = primops1; do_not_unfold_pure_lets = do_not_unfold_pure_lets; unfold_until = unfold_until; unfold_only = unfold_only; unfold_fully = unfold_fully; unfold_attr = unfold_attr; unfold_tac = unfold_tac; pure_subterms_within_computations = pure_subterms_within_computations; simplify = simplify1; erase_universes = erase_universes; allow_unbound_universes = allow_unbound_universes; reify_ = reify_1; compress_uvars = compress_uvars; no_full_norm = no_full_norm; check_no_uvars = check_no_uvars; unmeta = unmeta1; unascribe = unascribe1; in_full_norm_request = in_full_norm_request; weakly_reduce_scrutinee = weakly_reduce_scrutinee; nbe_step = nbe_step; for_extraction = for_extraction} -> begin
for_extraction
end))


let steps_to_string : fsteps  ->  Prims.string = (fun f -> (

let format_opt = (fun f1 o -> (match (o) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____1376 = (

let uu____1377 = (f1 x)
in (Prims.strcat uu____1377 ")"))
in (Prims.strcat "Some (" uu____1376))
end))
in (

let b = FStar_Util.string_of_bool
in (

let uu____1383 = (

let uu____1386 = (FStar_All.pipe_right f.beta b)
in (

let uu____1387 = (

let uu____1390 = (FStar_All.pipe_right f.iota b)
in (

let uu____1391 = (

let uu____1394 = (FStar_All.pipe_right f.zeta b)
in (

let uu____1395 = (

let uu____1398 = (FStar_All.pipe_right f.weak b)
in (

let uu____1399 = (

let uu____1402 = (FStar_All.pipe_right f.hnf b)
in (

let uu____1403 = (

let uu____1406 = (FStar_All.pipe_right f.primops b)
in (

let uu____1407 = (

let uu____1410 = (FStar_All.pipe_right f.do_not_unfold_pure_lets b)
in (

let uu____1411 = (

let uu____1414 = (FStar_All.pipe_right f.unfold_until (format_opt FStar_Syntax_Print.delta_depth_to_string))
in (

let uu____1417 = (

let uu____1420 = (FStar_All.pipe_right f.unfold_only (format_opt (fun x -> (

let uu____1432 = (FStar_List.map FStar_Ident.string_of_lid x)
in (FStar_All.pipe_right uu____1432 (FStar_String.concat ", "))))))
in (

let uu____1437 = (

let uu____1440 = (FStar_All.pipe_right f.unfold_fully (format_opt (fun x -> (

let uu____1452 = (FStar_List.map FStar_Ident.string_of_lid x)
in (FStar_All.pipe_right uu____1452 (FStar_String.concat ", "))))))
in (

let uu____1457 = (

let uu____1460 = (FStar_All.pipe_right f.unfold_attr (format_opt (fun x -> (

let uu____1472 = (FStar_List.map FStar_Ident.string_of_lid x)
in (FStar_All.pipe_right uu____1472 (FStar_String.concat ", "))))))
in (

let uu____1477 = (

let uu____1480 = (FStar_All.pipe_right f.unfold_tac b)
in (

let uu____1481 = (

let uu____1484 = (FStar_All.pipe_right f.pure_subterms_within_computations b)
in (

let uu____1485 = (

let uu____1488 = (FStar_All.pipe_right f.simplify b)
in (

let uu____1489 = (

let uu____1492 = (FStar_All.pipe_right f.erase_universes b)
in (

let uu____1493 = (

let uu____1496 = (FStar_All.pipe_right f.allow_unbound_universes b)
in (

let uu____1497 = (

let uu____1500 = (FStar_All.pipe_right f.reify_ b)
in (

let uu____1501 = (

let uu____1504 = (FStar_All.pipe_right f.compress_uvars b)
in (

let uu____1505 = (

let uu____1508 = (FStar_All.pipe_right f.no_full_norm b)
in (

let uu____1509 = (

let uu____1512 = (FStar_All.pipe_right f.check_no_uvars b)
in (

let uu____1513 = (

let uu____1516 = (FStar_All.pipe_right f.unmeta b)
in (

let uu____1517 = (

let uu____1520 = (FStar_All.pipe_right f.unascribe b)
in (

let uu____1521 = (

let uu____1524 = (FStar_All.pipe_right f.in_full_norm_request b)
in (

let uu____1525 = (

let uu____1528 = (FStar_All.pipe_right f.weakly_reduce_scrutinee b)
in (uu____1528)::[])
in (uu____1524)::uu____1525))
in (uu____1520)::uu____1521))
in (uu____1516)::uu____1517))
in (uu____1512)::uu____1513))
in (uu____1508)::uu____1509))
in (uu____1504)::uu____1505))
in (uu____1500)::uu____1501))
in (uu____1496)::uu____1497))
in (uu____1492)::uu____1493))
in (uu____1488)::uu____1489))
in (uu____1484)::uu____1485))
in (uu____1480)::uu____1481))
in (uu____1460)::uu____1477))
in (uu____1440)::uu____1457))
in (uu____1420)::uu____1437))
in (uu____1414)::uu____1417))
in (uu____1410)::uu____1411))
in (uu____1406)::uu____1407))
in (uu____1402)::uu____1403))
in (uu____1398)::uu____1399))
in (uu____1394)::uu____1395))
in (uu____1390)::uu____1391))
in (uu____1386)::uu____1387))
in (FStar_Util.format "{\nbeta = %s;\niota = %s;\nzeta = %s;\nweak = %s;\nhnf  = %s;\nprimops = %s;\ndo_not_unfold_pure_lets = %s;\nunfold_until = %s;\nunfold_only = %s;\nunfold_fully = %s;\nunfold_attr = %s;\nunfold_tac = %s;\npure_subterms_within_computations = %s;\nsimplify = %s;\nerase_universes = %s;\nallow_unbound_universes = %s;\nreify_ = %s;\ncompress_uvars = %s;\nno_full_norm = %s;\ncheck_no_uvars = %s;\nunmeta = %s;\nunascribe = %s;\nin_full_norm_request = %s;\nweakly_reduce_scrutinee = %s;\n}" uu____1383)))))


let default_steps : fsteps = {beta = true; iota = true; zeta = true; weak = false; hnf = false; primops = false; do_not_unfold_pure_lets = false; unfold_until = FStar_Pervasives_Native.None; unfold_only = FStar_Pervasives_Native.None; unfold_fully = FStar_Pervasives_Native.None; unfold_attr = FStar_Pervasives_Native.None; unfold_tac = false; pure_subterms_within_computations = false; simplify = false; erase_universes = false; allow_unbound_universes = false; reify_ = false; compress_uvars = false; no_full_norm = false; check_no_uvars = false; unmeta = false; unascribe = false; in_full_norm_request = false; weakly_reduce_scrutinee = true; nbe_step = false; for_extraction = false}


let fstep_add_one : FStar_TypeChecker_Env.step  ->  fsteps  ->  fsteps = (fun s fs -> (match (s) with
| FStar_TypeChecker_Env.Beta -> begin
(

let uu___238_1545 = fs
in {beta = true; iota = uu___238_1545.iota; zeta = uu___238_1545.zeta; weak = uu___238_1545.weak; hnf = uu___238_1545.hnf; primops = uu___238_1545.primops; do_not_unfold_pure_lets = uu___238_1545.do_not_unfold_pure_lets; unfold_until = uu___238_1545.unfold_until; unfold_only = uu___238_1545.unfold_only; unfold_fully = uu___238_1545.unfold_fully; unfold_attr = uu___238_1545.unfold_attr; unfold_tac = uu___238_1545.unfold_tac; pure_subterms_within_computations = uu___238_1545.pure_subterms_within_computations; simplify = uu___238_1545.simplify; erase_universes = uu___238_1545.erase_universes; allow_unbound_universes = uu___238_1545.allow_unbound_universes; reify_ = uu___238_1545.reify_; compress_uvars = uu___238_1545.compress_uvars; no_full_norm = uu___238_1545.no_full_norm; check_no_uvars = uu___238_1545.check_no_uvars; unmeta = uu___238_1545.unmeta; unascribe = uu___238_1545.unascribe; in_full_norm_request = uu___238_1545.in_full_norm_request; weakly_reduce_scrutinee = uu___238_1545.weakly_reduce_scrutinee; nbe_step = uu___238_1545.nbe_step; for_extraction = uu___238_1545.for_extraction})
end
| FStar_TypeChecker_Env.Iota -> begin
(

let uu___239_1546 = fs
in {beta = uu___239_1546.beta; iota = true; zeta = uu___239_1546.zeta; weak = uu___239_1546.weak; hnf = uu___239_1546.hnf; primops = uu___239_1546.primops; do_not_unfold_pure_lets = uu___239_1546.do_not_unfold_pure_lets; unfold_until = uu___239_1546.unfold_until; unfold_only = uu___239_1546.unfold_only; unfold_fully = uu___239_1546.unfold_fully; unfold_attr = uu___239_1546.unfold_attr; unfold_tac = uu___239_1546.unfold_tac; pure_subterms_within_computations = uu___239_1546.pure_subterms_within_computations; simplify = uu___239_1546.simplify; erase_universes = uu___239_1546.erase_universes; allow_unbound_universes = uu___239_1546.allow_unbound_universes; reify_ = uu___239_1546.reify_; compress_uvars = uu___239_1546.compress_uvars; no_full_norm = uu___239_1546.no_full_norm; check_no_uvars = uu___239_1546.check_no_uvars; unmeta = uu___239_1546.unmeta; unascribe = uu___239_1546.unascribe; in_full_norm_request = uu___239_1546.in_full_norm_request; weakly_reduce_scrutinee = uu___239_1546.weakly_reduce_scrutinee; nbe_step = uu___239_1546.nbe_step; for_extraction = uu___239_1546.for_extraction})
end
| FStar_TypeChecker_Env.Zeta -> begin
(

let uu___240_1547 = fs
in {beta = uu___240_1547.beta; iota = uu___240_1547.iota; zeta = true; weak = uu___240_1547.weak; hnf = uu___240_1547.hnf; primops = uu___240_1547.primops; do_not_unfold_pure_lets = uu___240_1547.do_not_unfold_pure_lets; unfold_until = uu___240_1547.unfold_until; unfold_only = uu___240_1547.unfold_only; unfold_fully = uu___240_1547.unfold_fully; unfold_attr = uu___240_1547.unfold_attr; unfold_tac = uu___240_1547.unfold_tac; pure_subterms_within_computations = uu___240_1547.pure_subterms_within_computations; simplify = uu___240_1547.simplify; erase_universes = uu___240_1547.erase_universes; allow_unbound_universes = uu___240_1547.allow_unbound_universes; reify_ = uu___240_1547.reify_; compress_uvars = uu___240_1547.compress_uvars; no_full_norm = uu___240_1547.no_full_norm; check_no_uvars = uu___240_1547.check_no_uvars; unmeta = uu___240_1547.unmeta; unascribe = uu___240_1547.unascribe; in_full_norm_request = uu___240_1547.in_full_norm_request; weakly_reduce_scrutinee = uu___240_1547.weakly_reduce_scrutinee; nbe_step = uu___240_1547.nbe_step; for_extraction = uu___240_1547.for_extraction})
end
| FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Beta) -> begin
(

let uu___241_1548 = fs
in {beta = false; iota = uu___241_1548.iota; zeta = uu___241_1548.zeta; weak = uu___241_1548.weak; hnf = uu___241_1548.hnf; primops = uu___241_1548.primops; do_not_unfold_pure_lets = uu___241_1548.do_not_unfold_pure_lets; unfold_until = uu___241_1548.unfold_until; unfold_only = uu___241_1548.unfold_only; unfold_fully = uu___241_1548.unfold_fully; unfold_attr = uu___241_1548.unfold_attr; unfold_tac = uu___241_1548.unfold_tac; pure_subterms_within_computations = uu___241_1548.pure_subterms_within_computations; simplify = uu___241_1548.simplify; erase_universes = uu___241_1548.erase_universes; allow_unbound_universes = uu___241_1548.allow_unbound_universes; reify_ = uu___241_1548.reify_; compress_uvars = uu___241_1548.compress_uvars; no_full_norm = uu___241_1548.no_full_norm; check_no_uvars = uu___241_1548.check_no_uvars; unmeta = uu___241_1548.unmeta; unascribe = uu___241_1548.unascribe; in_full_norm_request = uu___241_1548.in_full_norm_request; weakly_reduce_scrutinee = uu___241_1548.weakly_reduce_scrutinee; nbe_step = uu___241_1548.nbe_step; for_extraction = uu___241_1548.for_extraction})
end
| FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota) -> begin
(

let uu___242_1549 = fs
in {beta = uu___242_1549.beta; iota = false; zeta = uu___242_1549.zeta; weak = uu___242_1549.weak; hnf = uu___242_1549.hnf; primops = uu___242_1549.primops; do_not_unfold_pure_lets = uu___242_1549.do_not_unfold_pure_lets; unfold_until = uu___242_1549.unfold_until; unfold_only = uu___242_1549.unfold_only; unfold_fully = uu___242_1549.unfold_fully; unfold_attr = uu___242_1549.unfold_attr; unfold_tac = uu___242_1549.unfold_tac; pure_subterms_within_computations = uu___242_1549.pure_subterms_within_computations; simplify = uu___242_1549.simplify; erase_universes = uu___242_1549.erase_universes; allow_unbound_universes = uu___242_1549.allow_unbound_universes; reify_ = uu___242_1549.reify_; compress_uvars = uu___242_1549.compress_uvars; no_full_norm = uu___242_1549.no_full_norm; check_no_uvars = uu___242_1549.check_no_uvars; unmeta = uu___242_1549.unmeta; unascribe = uu___242_1549.unascribe; in_full_norm_request = uu___242_1549.in_full_norm_request; weakly_reduce_scrutinee = uu___242_1549.weakly_reduce_scrutinee; nbe_step = uu___242_1549.nbe_step; for_extraction = uu___242_1549.for_extraction})
end
| FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta) -> begin
(

let uu___243_1550 = fs
in {beta = uu___243_1550.beta; iota = uu___243_1550.iota; zeta = false; weak = uu___243_1550.weak; hnf = uu___243_1550.hnf; primops = uu___243_1550.primops; do_not_unfold_pure_lets = uu___243_1550.do_not_unfold_pure_lets; unfold_until = uu___243_1550.unfold_until; unfold_only = uu___243_1550.unfold_only; unfold_fully = uu___243_1550.unfold_fully; unfold_attr = uu___243_1550.unfold_attr; unfold_tac = uu___243_1550.unfold_tac; pure_subterms_within_computations = uu___243_1550.pure_subterms_within_computations; simplify = uu___243_1550.simplify; erase_universes = uu___243_1550.erase_universes; allow_unbound_universes = uu___243_1550.allow_unbound_universes; reify_ = uu___243_1550.reify_; compress_uvars = uu___243_1550.compress_uvars; no_full_norm = uu___243_1550.no_full_norm; check_no_uvars = uu___243_1550.check_no_uvars; unmeta = uu___243_1550.unmeta; unascribe = uu___243_1550.unascribe; in_full_norm_request = uu___243_1550.in_full_norm_request; weakly_reduce_scrutinee = uu___243_1550.weakly_reduce_scrutinee; nbe_step = uu___243_1550.nbe_step; for_extraction = uu___243_1550.for_extraction})
end
| FStar_TypeChecker_Env.Exclude (uu____1551) -> begin
(failwith "Bad exclude")
end
| FStar_TypeChecker_Env.Weak -> begin
(

let uu___244_1552 = fs
in {beta = uu___244_1552.beta; iota = uu___244_1552.iota; zeta = uu___244_1552.zeta; weak = true; hnf = uu___244_1552.hnf; primops = uu___244_1552.primops; do_not_unfold_pure_lets = uu___244_1552.do_not_unfold_pure_lets; unfold_until = uu___244_1552.unfold_until; unfold_only = uu___244_1552.unfold_only; unfold_fully = uu___244_1552.unfold_fully; unfold_attr = uu___244_1552.unfold_attr; unfold_tac = uu___244_1552.unfold_tac; pure_subterms_within_computations = uu___244_1552.pure_subterms_within_computations; simplify = uu___244_1552.simplify; erase_universes = uu___244_1552.erase_universes; allow_unbound_universes = uu___244_1552.allow_unbound_universes; reify_ = uu___244_1552.reify_; compress_uvars = uu___244_1552.compress_uvars; no_full_norm = uu___244_1552.no_full_norm; check_no_uvars = uu___244_1552.check_no_uvars; unmeta = uu___244_1552.unmeta; unascribe = uu___244_1552.unascribe; in_full_norm_request = uu___244_1552.in_full_norm_request; weakly_reduce_scrutinee = uu___244_1552.weakly_reduce_scrutinee; nbe_step = uu___244_1552.nbe_step; for_extraction = uu___244_1552.for_extraction})
end
| FStar_TypeChecker_Env.HNF -> begin
(

let uu___245_1553 = fs
in {beta = uu___245_1553.beta; iota = uu___245_1553.iota; zeta = uu___245_1553.zeta; weak = uu___245_1553.weak; hnf = true; primops = uu___245_1553.primops; do_not_unfold_pure_lets = uu___245_1553.do_not_unfold_pure_lets; unfold_until = uu___245_1553.unfold_until; unfold_only = uu___245_1553.unfold_only; unfold_fully = uu___245_1553.unfold_fully; unfold_attr = uu___245_1553.unfold_attr; unfold_tac = uu___245_1553.unfold_tac; pure_subterms_within_computations = uu___245_1553.pure_subterms_within_computations; simplify = uu___245_1553.simplify; erase_universes = uu___245_1553.erase_universes; allow_unbound_universes = uu___245_1553.allow_unbound_universes; reify_ = uu___245_1553.reify_; compress_uvars = uu___245_1553.compress_uvars; no_full_norm = uu___245_1553.no_full_norm; check_no_uvars = uu___245_1553.check_no_uvars; unmeta = uu___245_1553.unmeta; unascribe = uu___245_1553.unascribe; in_full_norm_request = uu___245_1553.in_full_norm_request; weakly_reduce_scrutinee = uu___245_1553.weakly_reduce_scrutinee; nbe_step = uu___245_1553.nbe_step; for_extraction = uu___245_1553.for_extraction})
end
| FStar_TypeChecker_Env.Primops -> begin
(

let uu___246_1554 = fs
in {beta = uu___246_1554.beta; iota = uu___246_1554.iota; zeta = uu___246_1554.zeta; weak = uu___246_1554.weak; hnf = uu___246_1554.hnf; primops = true; do_not_unfold_pure_lets = uu___246_1554.do_not_unfold_pure_lets; unfold_until = uu___246_1554.unfold_until; unfold_only = uu___246_1554.unfold_only; unfold_fully = uu___246_1554.unfold_fully; unfold_attr = uu___246_1554.unfold_attr; unfold_tac = uu___246_1554.unfold_tac; pure_subterms_within_computations = uu___246_1554.pure_subterms_within_computations; simplify = uu___246_1554.simplify; erase_universes = uu___246_1554.erase_universes; allow_unbound_universes = uu___246_1554.allow_unbound_universes; reify_ = uu___246_1554.reify_; compress_uvars = uu___246_1554.compress_uvars; no_full_norm = uu___246_1554.no_full_norm; check_no_uvars = uu___246_1554.check_no_uvars; unmeta = uu___246_1554.unmeta; unascribe = uu___246_1554.unascribe; in_full_norm_request = uu___246_1554.in_full_norm_request; weakly_reduce_scrutinee = uu___246_1554.weakly_reduce_scrutinee; nbe_step = uu___246_1554.nbe_step; for_extraction = uu___246_1554.for_extraction})
end
| FStar_TypeChecker_Env.Eager_unfolding -> begin
fs
end
| FStar_TypeChecker_Env.Inlining -> begin
fs
end
| FStar_TypeChecker_Env.DoNotUnfoldPureLets -> begin
(

let uu___247_1555 = fs
in {beta = uu___247_1555.beta; iota = uu___247_1555.iota; zeta = uu___247_1555.zeta; weak = uu___247_1555.weak; hnf = uu___247_1555.hnf; primops = uu___247_1555.primops; do_not_unfold_pure_lets = true; unfold_until = uu___247_1555.unfold_until; unfold_only = uu___247_1555.unfold_only; unfold_fully = uu___247_1555.unfold_fully; unfold_attr = uu___247_1555.unfold_attr; unfold_tac = uu___247_1555.unfold_tac; pure_subterms_within_computations = uu___247_1555.pure_subterms_within_computations; simplify = uu___247_1555.simplify; erase_universes = uu___247_1555.erase_universes; allow_unbound_universes = uu___247_1555.allow_unbound_universes; reify_ = uu___247_1555.reify_; compress_uvars = uu___247_1555.compress_uvars; no_full_norm = uu___247_1555.no_full_norm; check_no_uvars = uu___247_1555.check_no_uvars; unmeta = uu___247_1555.unmeta; unascribe = uu___247_1555.unascribe; in_full_norm_request = uu___247_1555.in_full_norm_request; weakly_reduce_scrutinee = uu___247_1555.weakly_reduce_scrutinee; nbe_step = uu___247_1555.nbe_step; for_extraction = uu___247_1555.for_extraction})
end
| FStar_TypeChecker_Env.UnfoldUntil (d) -> begin
(

let uu___248_1557 = fs
in {beta = uu___248_1557.beta; iota = uu___248_1557.iota; zeta = uu___248_1557.zeta; weak = uu___248_1557.weak; hnf = uu___248_1557.hnf; primops = uu___248_1557.primops; do_not_unfold_pure_lets = uu___248_1557.do_not_unfold_pure_lets; unfold_until = FStar_Pervasives_Native.Some (d); unfold_only = uu___248_1557.unfold_only; unfold_fully = uu___248_1557.unfold_fully; unfold_attr = uu___248_1557.unfold_attr; unfold_tac = uu___248_1557.unfold_tac; pure_subterms_within_computations = uu___248_1557.pure_subterms_within_computations; simplify = uu___248_1557.simplify; erase_universes = uu___248_1557.erase_universes; allow_unbound_universes = uu___248_1557.allow_unbound_universes; reify_ = uu___248_1557.reify_; compress_uvars = uu___248_1557.compress_uvars; no_full_norm = uu___248_1557.no_full_norm; check_no_uvars = uu___248_1557.check_no_uvars; unmeta = uu___248_1557.unmeta; unascribe = uu___248_1557.unascribe; in_full_norm_request = uu___248_1557.in_full_norm_request; weakly_reduce_scrutinee = uu___248_1557.weakly_reduce_scrutinee; nbe_step = uu___248_1557.nbe_step; for_extraction = uu___248_1557.for_extraction})
end
| FStar_TypeChecker_Env.UnfoldOnly (lids) -> begin
(

let uu___249_1561 = fs
in {beta = uu___249_1561.beta; iota = uu___249_1561.iota; zeta = uu___249_1561.zeta; weak = uu___249_1561.weak; hnf = uu___249_1561.hnf; primops = uu___249_1561.primops; do_not_unfold_pure_lets = uu___249_1561.do_not_unfold_pure_lets; unfold_until = uu___249_1561.unfold_until; unfold_only = FStar_Pervasives_Native.Some (lids); unfold_fully = uu___249_1561.unfold_fully; unfold_attr = uu___249_1561.unfold_attr; unfold_tac = uu___249_1561.unfold_tac; pure_subterms_within_computations = uu___249_1561.pure_subterms_within_computations; simplify = uu___249_1561.simplify; erase_universes = uu___249_1561.erase_universes; allow_unbound_universes = uu___249_1561.allow_unbound_universes; reify_ = uu___249_1561.reify_; compress_uvars = uu___249_1561.compress_uvars; no_full_norm = uu___249_1561.no_full_norm; check_no_uvars = uu___249_1561.check_no_uvars; unmeta = uu___249_1561.unmeta; unascribe = uu___249_1561.unascribe; in_full_norm_request = uu___249_1561.in_full_norm_request; weakly_reduce_scrutinee = uu___249_1561.weakly_reduce_scrutinee; nbe_step = uu___249_1561.nbe_step; for_extraction = uu___249_1561.for_extraction})
end
| FStar_TypeChecker_Env.UnfoldFully (lids) -> begin
(

let uu___250_1567 = fs
in {beta = uu___250_1567.beta; iota = uu___250_1567.iota; zeta = uu___250_1567.zeta; weak = uu___250_1567.weak; hnf = uu___250_1567.hnf; primops = uu___250_1567.primops; do_not_unfold_pure_lets = uu___250_1567.do_not_unfold_pure_lets; unfold_until = uu___250_1567.unfold_until; unfold_only = uu___250_1567.unfold_only; unfold_fully = FStar_Pervasives_Native.Some (lids); unfold_attr = uu___250_1567.unfold_attr; unfold_tac = uu___250_1567.unfold_tac; pure_subterms_within_computations = uu___250_1567.pure_subterms_within_computations; simplify = uu___250_1567.simplify; erase_universes = uu___250_1567.erase_universes; allow_unbound_universes = uu___250_1567.allow_unbound_universes; reify_ = uu___250_1567.reify_; compress_uvars = uu___250_1567.compress_uvars; no_full_norm = uu___250_1567.no_full_norm; check_no_uvars = uu___250_1567.check_no_uvars; unmeta = uu___250_1567.unmeta; unascribe = uu___250_1567.unascribe; in_full_norm_request = uu___250_1567.in_full_norm_request; weakly_reduce_scrutinee = uu___250_1567.weakly_reduce_scrutinee; nbe_step = uu___250_1567.nbe_step; for_extraction = uu___250_1567.for_extraction})
end
| FStar_TypeChecker_Env.UnfoldAttr (lids) -> begin
(

let uu___251_1573 = fs
in {beta = uu___251_1573.beta; iota = uu___251_1573.iota; zeta = uu___251_1573.zeta; weak = uu___251_1573.weak; hnf = uu___251_1573.hnf; primops = uu___251_1573.primops; do_not_unfold_pure_lets = uu___251_1573.do_not_unfold_pure_lets; unfold_until = uu___251_1573.unfold_until; unfold_only = uu___251_1573.unfold_only; unfold_fully = uu___251_1573.unfold_fully; unfold_attr = FStar_Pervasives_Native.Some (lids); unfold_tac = uu___251_1573.unfold_tac; pure_subterms_within_computations = uu___251_1573.pure_subterms_within_computations; simplify = uu___251_1573.simplify; erase_universes = uu___251_1573.erase_universes; allow_unbound_universes = uu___251_1573.allow_unbound_universes; reify_ = uu___251_1573.reify_; compress_uvars = uu___251_1573.compress_uvars; no_full_norm = uu___251_1573.no_full_norm; check_no_uvars = uu___251_1573.check_no_uvars; unmeta = uu___251_1573.unmeta; unascribe = uu___251_1573.unascribe; in_full_norm_request = uu___251_1573.in_full_norm_request; weakly_reduce_scrutinee = uu___251_1573.weakly_reduce_scrutinee; nbe_step = uu___251_1573.nbe_step; for_extraction = uu___251_1573.for_extraction})
end
| FStar_TypeChecker_Env.UnfoldTac -> begin
(

let uu___252_1576 = fs
in {beta = uu___252_1576.beta; iota = uu___252_1576.iota; zeta = uu___252_1576.zeta; weak = uu___252_1576.weak; hnf = uu___252_1576.hnf; primops = uu___252_1576.primops; do_not_unfold_pure_lets = uu___252_1576.do_not_unfold_pure_lets; unfold_until = uu___252_1576.unfold_until; unfold_only = uu___252_1576.unfold_only; unfold_fully = uu___252_1576.unfold_fully; unfold_attr = uu___252_1576.unfold_attr; unfold_tac = true; pure_subterms_within_computations = uu___252_1576.pure_subterms_within_computations; simplify = uu___252_1576.simplify; erase_universes = uu___252_1576.erase_universes; allow_unbound_universes = uu___252_1576.allow_unbound_universes; reify_ = uu___252_1576.reify_; compress_uvars = uu___252_1576.compress_uvars; no_full_norm = uu___252_1576.no_full_norm; check_no_uvars = uu___252_1576.check_no_uvars; unmeta = uu___252_1576.unmeta; unascribe = uu___252_1576.unascribe; in_full_norm_request = uu___252_1576.in_full_norm_request; weakly_reduce_scrutinee = uu___252_1576.weakly_reduce_scrutinee; nbe_step = uu___252_1576.nbe_step; for_extraction = uu___252_1576.for_extraction})
end
| FStar_TypeChecker_Env.PureSubtermsWithinComputations -> begin
(

let uu___253_1577 = fs
in {beta = uu___253_1577.beta; iota = uu___253_1577.iota; zeta = uu___253_1577.zeta; weak = uu___253_1577.weak; hnf = uu___253_1577.hnf; primops = uu___253_1577.primops; do_not_unfold_pure_lets = uu___253_1577.do_not_unfold_pure_lets; unfold_until = uu___253_1577.unfold_until; unfold_only = uu___253_1577.unfold_only; unfold_fully = uu___253_1577.unfold_fully; unfold_attr = uu___253_1577.unfold_attr; unfold_tac = uu___253_1577.unfold_tac; pure_subterms_within_computations = true; simplify = uu___253_1577.simplify; erase_universes = uu___253_1577.erase_universes; allow_unbound_universes = uu___253_1577.allow_unbound_universes; reify_ = uu___253_1577.reify_; compress_uvars = uu___253_1577.compress_uvars; no_full_norm = uu___253_1577.no_full_norm; check_no_uvars = uu___253_1577.check_no_uvars; unmeta = uu___253_1577.unmeta; unascribe = uu___253_1577.unascribe; in_full_norm_request = uu___253_1577.in_full_norm_request; weakly_reduce_scrutinee = uu___253_1577.weakly_reduce_scrutinee; nbe_step = uu___253_1577.nbe_step; for_extraction = uu___253_1577.for_extraction})
end
| FStar_TypeChecker_Env.Simplify -> begin
(

let uu___254_1578 = fs
in {beta = uu___254_1578.beta; iota = uu___254_1578.iota; zeta = uu___254_1578.zeta; weak = uu___254_1578.weak; hnf = uu___254_1578.hnf; primops = uu___254_1578.primops; do_not_unfold_pure_lets = uu___254_1578.do_not_unfold_pure_lets; unfold_until = uu___254_1578.unfold_until; unfold_only = uu___254_1578.unfold_only; unfold_fully = uu___254_1578.unfold_fully; unfold_attr = uu___254_1578.unfold_attr; unfold_tac = uu___254_1578.unfold_tac; pure_subterms_within_computations = uu___254_1578.pure_subterms_within_computations; simplify = true; erase_universes = uu___254_1578.erase_universes; allow_unbound_universes = uu___254_1578.allow_unbound_universes; reify_ = uu___254_1578.reify_; compress_uvars = uu___254_1578.compress_uvars; no_full_norm = uu___254_1578.no_full_norm; check_no_uvars = uu___254_1578.check_no_uvars; unmeta = uu___254_1578.unmeta; unascribe = uu___254_1578.unascribe; in_full_norm_request = uu___254_1578.in_full_norm_request; weakly_reduce_scrutinee = uu___254_1578.weakly_reduce_scrutinee; nbe_step = uu___254_1578.nbe_step; for_extraction = uu___254_1578.for_extraction})
end
| FStar_TypeChecker_Env.EraseUniverses -> begin
(

let uu___255_1579 = fs
in {beta = uu___255_1579.beta; iota = uu___255_1579.iota; zeta = uu___255_1579.zeta; weak = uu___255_1579.weak; hnf = uu___255_1579.hnf; primops = uu___255_1579.primops; do_not_unfold_pure_lets = uu___255_1579.do_not_unfold_pure_lets; unfold_until = uu___255_1579.unfold_until; unfold_only = uu___255_1579.unfold_only; unfold_fully = uu___255_1579.unfold_fully; unfold_attr = uu___255_1579.unfold_attr; unfold_tac = uu___255_1579.unfold_tac; pure_subterms_within_computations = uu___255_1579.pure_subterms_within_computations; simplify = uu___255_1579.simplify; erase_universes = true; allow_unbound_universes = uu___255_1579.allow_unbound_universes; reify_ = uu___255_1579.reify_; compress_uvars = uu___255_1579.compress_uvars; no_full_norm = uu___255_1579.no_full_norm; check_no_uvars = uu___255_1579.check_no_uvars; unmeta = uu___255_1579.unmeta; unascribe = uu___255_1579.unascribe; in_full_norm_request = uu___255_1579.in_full_norm_request; weakly_reduce_scrutinee = uu___255_1579.weakly_reduce_scrutinee; nbe_step = uu___255_1579.nbe_step; for_extraction = uu___255_1579.for_extraction})
end
| FStar_TypeChecker_Env.AllowUnboundUniverses -> begin
(

let uu___256_1580 = fs
in {beta = uu___256_1580.beta; iota = uu___256_1580.iota; zeta = uu___256_1580.zeta; weak = uu___256_1580.weak; hnf = uu___256_1580.hnf; primops = uu___256_1580.primops; do_not_unfold_pure_lets = uu___256_1580.do_not_unfold_pure_lets; unfold_until = uu___256_1580.unfold_until; unfold_only = uu___256_1580.unfold_only; unfold_fully = uu___256_1580.unfold_fully; unfold_attr = uu___256_1580.unfold_attr; unfold_tac = uu___256_1580.unfold_tac; pure_subterms_within_computations = uu___256_1580.pure_subterms_within_computations; simplify = uu___256_1580.simplify; erase_universes = uu___256_1580.erase_universes; allow_unbound_universes = true; reify_ = uu___256_1580.reify_; compress_uvars = uu___256_1580.compress_uvars; no_full_norm = uu___256_1580.no_full_norm; check_no_uvars = uu___256_1580.check_no_uvars; unmeta = uu___256_1580.unmeta; unascribe = uu___256_1580.unascribe; in_full_norm_request = uu___256_1580.in_full_norm_request; weakly_reduce_scrutinee = uu___256_1580.weakly_reduce_scrutinee; nbe_step = uu___256_1580.nbe_step; for_extraction = uu___256_1580.for_extraction})
end
| FStar_TypeChecker_Env.Reify -> begin
(

let uu___257_1581 = fs
in {beta = uu___257_1581.beta; iota = uu___257_1581.iota; zeta = uu___257_1581.zeta; weak = uu___257_1581.weak; hnf = uu___257_1581.hnf; primops = uu___257_1581.primops; do_not_unfold_pure_lets = uu___257_1581.do_not_unfold_pure_lets; unfold_until = uu___257_1581.unfold_until; unfold_only = uu___257_1581.unfold_only; unfold_fully = uu___257_1581.unfold_fully; unfold_attr = uu___257_1581.unfold_attr; unfold_tac = uu___257_1581.unfold_tac; pure_subterms_within_computations = uu___257_1581.pure_subterms_within_computations; simplify = uu___257_1581.simplify; erase_universes = uu___257_1581.erase_universes; allow_unbound_universes = uu___257_1581.allow_unbound_universes; reify_ = true; compress_uvars = uu___257_1581.compress_uvars; no_full_norm = uu___257_1581.no_full_norm; check_no_uvars = uu___257_1581.check_no_uvars; unmeta = uu___257_1581.unmeta; unascribe = uu___257_1581.unascribe; in_full_norm_request = uu___257_1581.in_full_norm_request; weakly_reduce_scrutinee = uu___257_1581.weakly_reduce_scrutinee; nbe_step = uu___257_1581.nbe_step; for_extraction = uu___257_1581.for_extraction})
end
| FStar_TypeChecker_Env.CompressUvars -> begin
(

let uu___258_1582 = fs
in {beta = uu___258_1582.beta; iota = uu___258_1582.iota; zeta = uu___258_1582.zeta; weak = uu___258_1582.weak; hnf = uu___258_1582.hnf; primops = uu___258_1582.primops; do_not_unfold_pure_lets = uu___258_1582.do_not_unfold_pure_lets; unfold_until = uu___258_1582.unfold_until; unfold_only = uu___258_1582.unfold_only; unfold_fully = uu___258_1582.unfold_fully; unfold_attr = uu___258_1582.unfold_attr; unfold_tac = uu___258_1582.unfold_tac; pure_subterms_within_computations = uu___258_1582.pure_subterms_within_computations; simplify = uu___258_1582.simplify; erase_universes = uu___258_1582.erase_universes; allow_unbound_universes = uu___258_1582.allow_unbound_universes; reify_ = uu___258_1582.reify_; compress_uvars = true; no_full_norm = uu___258_1582.no_full_norm; check_no_uvars = uu___258_1582.check_no_uvars; unmeta = uu___258_1582.unmeta; unascribe = uu___258_1582.unascribe; in_full_norm_request = uu___258_1582.in_full_norm_request; weakly_reduce_scrutinee = uu___258_1582.weakly_reduce_scrutinee; nbe_step = uu___258_1582.nbe_step; for_extraction = uu___258_1582.for_extraction})
end
| FStar_TypeChecker_Env.NoFullNorm -> begin
(

let uu___259_1583 = fs
in {beta = uu___259_1583.beta; iota = uu___259_1583.iota; zeta = uu___259_1583.zeta; weak = uu___259_1583.weak; hnf = uu___259_1583.hnf; primops = uu___259_1583.primops; do_not_unfold_pure_lets = uu___259_1583.do_not_unfold_pure_lets; unfold_until = uu___259_1583.unfold_until; unfold_only = uu___259_1583.unfold_only; unfold_fully = uu___259_1583.unfold_fully; unfold_attr = uu___259_1583.unfold_attr; unfold_tac = uu___259_1583.unfold_tac; pure_subterms_within_computations = uu___259_1583.pure_subterms_within_computations; simplify = uu___259_1583.simplify; erase_universes = uu___259_1583.erase_universes; allow_unbound_universes = uu___259_1583.allow_unbound_universes; reify_ = uu___259_1583.reify_; compress_uvars = uu___259_1583.compress_uvars; no_full_norm = true; check_no_uvars = uu___259_1583.check_no_uvars; unmeta = uu___259_1583.unmeta; unascribe = uu___259_1583.unascribe; in_full_norm_request = uu___259_1583.in_full_norm_request; weakly_reduce_scrutinee = uu___259_1583.weakly_reduce_scrutinee; nbe_step = uu___259_1583.nbe_step; for_extraction = uu___259_1583.for_extraction})
end
| FStar_TypeChecker_Env.CheckNoUvars -> begin
(

let uu___260_1584 = fs
in {beta = uu___260_1584.beta; iota = uu___260_1584.iota; zeta = uu___260_1584.zeta; weak = uu___260_1584.weak; hnf = uu___260_1584.hnf; primops = uu___260_1584.primops; do_not_unfold_pure_lets = uu___260_1584.do_not_unfold_pure_lets; unfold_until = uu___260_1584.unfold_until; unfold_only = uu___260_1584.unfold_only; unfold_fully = uu___260_1584.unfold_fully; unfold_attr = uu___260_1584.unfold_attr; unfold_tac = uu___260_1584.unfold_tac; pure_subterms_within_computations = uu___260_1584.pure_subterms_within_computations; simplify = uu___260_1584.simplify; erase_universes = uu___260_1584.erase_universes; allow_unbound_universes = uu___260_1584.allow_unbound_universes; reify_ = uu___260_1584.reify_; compress_uvars = uu___260_1584.compress_uvars; no_full_norm = uu___260_1584.no_full_norm; check_no_uvars = true; unmeta = uu___260_1584.unmeta; unascribe = uu___260_1584.unascribe; in_full_norm_request = uu___260_1584.in_full_norm_request; weakly_reduce_scrutinee = uu___260_1584.weakly_reduce_scrutinee; nbe_step = uu___260_1584.nbe_step; for_extraction = uu___260_1584.for_extraction})
end
| FStar_TypeChecker_Env.Unmeta -> begin
(

let uu___261_1585 = fs
in {beta = uu___261_1585.beta; iota = uu___261_1585.iota; zeta = uu___261_1585.zeta; weak = uu___261_1585.weak; hnf = uu___261_1585.hnf; primops = uu___261_1585.primops; do_not_unfold_pure_lets = uu___261_1585.do_not_unfold_pure_lets; unfold_until = uu___261_1585.unfold_until; unfold_only = uu___261_1585.unfold_only; unfold_fully = uu___261_1585.unfold_fully; unfold_attr = uu___261_1585.unfold_attr; unfold_tac = uu___261_1585.unfold_tac; pure_subterms_within_computations = uu___261_1585.pure_subterms_within_computations; simplify = uu___261_1585.simplify; erase_universes = uu___261_1585.erase_universes; allow_unbound_universes = uu___261_1585.allow_unbound_universes; reify_ = uu___261_1585.reify_; compress_uvars = uu___261_1585.compress_uvars; no_full_norm = uu___261_1585.no_full_norm; check_no_uvars = uu___261_1585.check_no_uvars; unmeta = true; unascribe = uu___261_1585.unascribe; in_full_norm_request = uu___261_1585.in_full_norm_request; weakly_reduce_scrutinee = uu___261_1585.weakly_reduce_scrutinee; nbe_step = uu___261_1585.nbe_step; for_extraction = uu___261_1585.for_extraction})
end
| FStar_TypeChecker_Env.Unascribe -> begin
(

let uu___262_1586 = fs
in {beta = uu___262_1586.beta; iota = uu___262_1586.iota; zeta = uu___262_1586.zeta; weak = uu___262_1586.weak; hnf = uu___262_1586.hnf; primops = uu___262_1586.primops; do_not_unfold_pure_lets = uu___262_1586.do_not_unfold_pure_lets; unfold_until = uu___262_1586.unfold_until; unfold_only = uu___262_1586.unfold_only; unfold_fully = uu___262_1586.unfold_fully; unfold_attr = uu___262_1586.unfold_attr; unfold_tac = uu___262_1586.unfold_tac; pure_subterms_within_computations = uu___262_1586.pure_subterms_within_computations; simplify = uu___262_1586.simplify; erase_universes = uu___262_1586.erase_universes; allow_unbound_universes = uu___262_1586.allow_unbound_universes; reify_ = uu___262_1586.reify_; compress_uvars = uu___262_1586.compress_uvars; no_full_norm = uu___262_1586.no_full_norm; check_no_uvars = uu___262_1586.check_no_uvars; unmeta = uu___262_1586.unmeta; unascribe = true; in_full_norm_request = uu___262_1586.in_full_norm_request; weakly_reduce_scrutinee = uu___262_1586.weakly_reduce_scrutinee; nbe_step = uu___262_1586.nbe_step; for_extraction = uu___262_1586.for_extraction})
end
| FStar_TypeChecker_Env.NBE -> begin
(

let uu___263_1587 = fs
in {beta = uu___263_1587.beta; iota = uu___263_1587.iota; zeta = uu___263_1587.zeta; weak = uu___263_1587.weak; hnf = uu___263_1587.hnf; primops = uu___263_1587.primops; do_not_unfold_pure_lets = uu___263_1587.do_not_unfold_pure_lets; unfold_until = uu___263_1587.unfold_until; unfold_only = uu___263_1587.unfold_only; unfold_fully = uu___263_1587.unfold_fully; unfold_attr = uu___263_1587.unfold_attr; unfold_tac = uu___263_1587.unfold_tac; pure_subterms_within_computations = uu___263_1587.pure_subterms_within_computations; simplify = uu___263_1587.simplify; erase_universes = uu___263_1587.erase_universes; allow_unbound_universes = uu___263_1587.allow_unbound_universes; reify_ = uu___263_1587.reify_; compress_uvars = uu___263_1587.compress_uvars; no_full_norm = uu___263_1587.no_full_norm; check_no_uvars = uu___263_1587.check_no_uvars; unmeta = uu___263_1587.unmeta; unascribe = uu___263_1587.unascribe; in_full_norm_request = uu___263_1587.in_full_norm_request; weakly_reduce_scrutinee = uu___263_1587.weakly_reduce_scrutinee; nbe_step = true; for_extraction = uu___263_1587.for_extraction})
end
| FStar_TypeChecker_Env.ForExtraction -> begin
(

let uu___264_1588 = fs
in {beta = uu___264_1588.beta; iota = uu___264_1588.iota; zeta = uu___264_1588.zeta; weak = uu___264_1588.weak; hnf = uu___264_1588.hnf; primops = uu___264_1588.primops; do_not_unfold_pure_lets = uu___264_1588.do_not_unfold_pure_lets; unfold_until = uu___264_1588.unfold_until; unfold_only = uu___264_1588.unfold_only; unfold_fully = uu___264_1588.unfold_fully; unfold_attr = uu___264_1588.unfold_attr; unfold_tac = uu___264_1588.unfold_tac; pure_subterms_within_computations = uu___264_1588.pure_subterms_within_computations; simplify = uu___264_1588.simplify; erase_universes = uu___264_1588.erase_universes; allow_unbound_universes = uu___264_1588.allow_unbound_universes; reify_ = uu___264_1588.reify_; compress_uvars = uu___264_1588.compress_uvars; no_full_norm = uu___264_1588.no_full_norm; check_no_uvars = uu___264_1588.check_no_uvars; unmeta = uu___264_1588.unmeta; unascribe = uu___264_1588.unascribe; in_full_norm_request = uu___264_1588.in_full_norm_request; weakly_reduce_scrutinee = uu___264_1588.weakly_reduce_scrutinee; nbe_step = uu___264_1588.nbe_step; for_extraction = true})
end))


let to_fsteps : FStar_TypeChecker_Env.step Prims.list  ->  fsteps = (fun s -> (FStar_List.fold_right fstep_add_one s default_steps))

type psc =
{psc_range : FStar_Range.range; psc_subst : unit  ->  FStar_Syntax_Syntax.subst_t}


let __proj__Mkpsc__item__psc_range : psc  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {psc_range = psc_range; psc_subst = psc_subst} -> begin
psc_range
end))


let __proj__Mkpsc__item__psc_subst : psc  ->  unit  ->  FStar_Syntax_Syntax.subst_t = (fun projectee -> (match (projectee) with
| {psc_range = psc_range; psc_subst = psc_subst} -> begin
psc_subst
end))


let null_psc : psc = {psc_range = FStar_Range.dummyRange; psc_subst = (fun uu____1641 -> [])}


let psc_range : psc  ->  FStar_Range.range = (fun psc -> psc.psc_range)


let psc_subst : psc  ->  FStar_Syntax_Syntax.subst_t = (fun psc -> (psc.psc_subst ()))

type debug_switches =
{gen : Prims.bool; top : Prims.bool; cfg : Prims.bool; primop : Prims.bool; unfolding : Prims.bool; b380 : Prims.bool; wpe : Prims.bool; norm_delayed : Prims.bool; print_normalized : Prims.bool}


let __proj__Mkdebug_switches__item__gen : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = gen1; top = top; cfg = cfg; primop = primop; unfolding = unfolding; b380 = b380; wpe = wpe; norm_delayed = norm_delayed; print_normalized = print_normalized} -> begin
gen1
end))


let __proj__Mkdebug_switches__item__top : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = gen1; top = top; cfg = cfg; primop = primop; unfolding = unfolding; b380 = b380; wpe = wpe; norm_delayed = norm_delayed; print_normalized = print_normalized} -> begin
top
end))


let __proj__Mkdebug_switches__item__cfg : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = gen1; top = top; cfg = cfg; primop = primop; unfolding = unfolding; b380 = b380; wpe = wpe; norm_delayed = norm_delayed; print_normalized = print_normalized} -> begin
cfg
end))


let __proj__Mkdebug_switches__item__primop : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = gen1; top = top; cfg = cfg; primop = primop; unfolding = unfolding; b380 = b380; wpe = wpe; norm_delayed = norm_delayed; print_normalized = print_normalized} -> begin
primop
end))


let __proj__Mkdebug_switches__item__unfolding : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = gen1; top = top; cfg = cfg; primop = primop; unfolding = unfolding; b380 = b380; wpe = wpe; norm_delayed = norm_delayed; print_normalized = print_normalized} -> begin
unfolding
end))


let __proj__Mkdebug_switches__item__b380 : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = gen1; top = top; cfg = cfg; primop = primop; unfolding = unfolding; b380 = b380; wpe = wpe; norm_delayed = norm_delayed; print_normalized = print_normalized} -> begin
b380
end))


let __proj__Mkdebug_switches__item__wpe : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = gen1; top = top; cfg = cfg; primop = primop; unfolding = unfolding; b380 = b380; wpe = wpe; norm_delayed = norm_delayed; print_normalized = print_normalized} -> begin
wpe
end))


let __proj__Mkdebug_switches__item__norm_delayed : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = gen1; top = top; cfg = cfg; primop = primop; unfolding = unfolding; b380 = b380; wpe = wpe; norm_delayed = norm_delayed; print_normalized = print_normalized} -> begin
norm_delayed
end))


let __proj__Mkdebug_switches__item__print_normalized : debug_switches  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {gen = gen1; top = top; cfg = cfg; primop = primop; unfolding = unfolding; b380 = b380; wpe = wpe; norm_delayed = norm_delayed; print_normalized = print_normalized} -> begin
print_normalized
end))

type primitive_step =
{name : FStar_Ident.lid; arity : Prims.int; univ_arity : Prims.int; auto_reflect : Prims.int FStar_Pervasives_Native.option; strong_reduction_ok : Prims.bool; requires_binder_substitution : Prims.bool; interpretation : psc  ->  FStar_Syntax_Embeddings.norm_cb  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option; interpretation_nbe : FStar_TypeChecker_NBETerm.nbe_cbs  ->  FStar_TypeChecker_NBETerm.args  ->  FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option}


let __proj__Mkprimitive_step__item__name : primitive_step  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| {name = name; arity = arity; univ_arity = univ_arity; auto_reflect = auto_reflect; strong_reduction_ok = strong_reduction_ok; requires_binder_substitution = requires_binder_substitution; interpretation = interpretation; interpretation_nbe = interpretation_nbe} -> begin
name
end))


let __proj__Mkprimitive_step__item__arity : primitive_step  ->  Prims.int = (fun projectee -> (match (projectee) with
| {name = name; arity = arity; univ_arity = univ_arity; auto_reflect = auto_reflect; strong_reduction_ok = strong_reduction_ok; requires_binder_substitution = requires_binder_substitution; interpretation = interpretation; interpretation_nbe = interpretation_nbe} -> begin
arity
end))


let __proj__Mkprimitive_step__item__univ_arity : primitive_step  ->  Prims.int = (fun projectee -> (match (projectee) with
| {name = name; arity = arity; univ_arity = univ_arity; auto_reflect = auto_reflect; strong_reduction_ok = strong_reduction_ok; requires_binder_substitution = requires_binder_substitution; interpretation = interpretation; interpretation_nbe = interpretation_nbe} -> begin
univ_arity
end))


let __proj__Mkprimitive_step__item__auto_reflect : primitive_step  ->  Prims.int FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {name = name; arity = arity; univ_arity = univ_arity; auto_reflect = auto_reflect; strong_reduction_ok = strong_reduction_ok; requires_binder_substitution = requires_binder_substitution; interpretation = interpretation; interpretation_nbe = interpretation_nbe} -> begin
auto_reflect
end))


let __proj__Mkprimitive_step__item__strong_reduction_ok : primitive_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {name = name; arity = arity; univ_arity = univ_arity; auto_reflect = auto_reflect; strong_reduction_ok = strong_reduction_ok; requires_binder_substitution = requires_binder_substitution; interpretation = interpretation; interpretation_nbe = interpretation_nbe} -> begin
strong_reduction_ok
end))


let __proj__Mkprimitive_step__item__requires_binder_substitution : primitive_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {name = name; arity = arity; univ_arity = univ_arity; auto_reflect = auto_reflect; strong_reduction_ok = strong_reduction_ok; requires_binder_substitution = requires_binder_substitution; interpretation = interpretation; interpretation_nbe = interpretation_nbe} -> begin
requires_binder_substitution
end))


let __proj__Mkprimitive_step__item__interpretation : primitive_step  ->  psc  ->  FStar_Syntax_Embeddings.norm_cb  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {name = name; arity = arity; univ_arity = univ_arity; auto_reflect = auto_reflect; strong_reduction_ok = strong_reduction_ok; requires_binder_substitution = requires_binder_substitution; interpretation = interpretation; interpretation_nbe = interpretation_nbe} -> begin
interpretation
end))


let __proj__Mkprimitive_step__item__interpretation_nbe : primitive_step  ->  FStar_TypeChecker_NBETerm.nbe_cbs  ->  FStar_TypeChecker_NBETerm.args  ->  FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {name = name; arity = arity; univ_arity = univ_arity; auto_reflect = auto_reflect; strong_reduction_ok = strong_reduction_ok; requires_binder_substitution = requires_binder_substitution; interpretation = interpretation; interpretation_nbe = interpretation_nbe} -> begin
interpretation_nbe
end))

type cfg =
{steps : fsteps; tcenv : FStar_TypeChecker_Env.env; debug : debug_switches; delta_level : FStar_TypeChecker_Env.delta_level Prims.list; primitive_steps : primitive_step FStar_Util.psmap; strong : Prims.bool; memoize_lazy : Prims.bool; normalize_pure_lets : Prims.bool; reifying : Prims.bool}


let __proj__Mkcfg__item__steps : cfg  ->  fsteps = (fun projectee -> (match (projectee) with
| {steps = steps; tcenv = tcenv; debug = debug1; delta_level = delta_level; primitive_steps = primitive_steps; strong = strong; memoize_lazy = memoize_lazy; normalize_pure_lets = normalize_pure_lets; reifying = reifying} -> begin
steps
end))


let __proj__Mkcfg__item__tcenv : cfg  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {steps = steps; tcenv = tcenv; debug = debug1; delta_level = delta_level; primitive_steps = primitive_steps; strong = strong; memoize_lazy = memoize_lazy; normalize_pure_lets = normalize_pure_lets; reifying = reifying} -> begin
tcenv
end))


let __proj__Mkcfg__item__debug : cfg  ->  debug_switches = (fun projectee -> (match (projectee) with
| {steps = steps; tcenv = tcenv; debug = debug1; delta_level = delta_level; primitive_steps = primitive_steps; strong = strong; memoize_lazy = memoize_lazy; normalize_pure_lets = normalize_pure_lets; reifying = reifying} -> begin
debug1
end))


let __proj__Mkcfg__item__delta_level : cfg  ->  FStar_TypeChecker_Env.delta_level Prims.list = (fun projectee -> (match (projectee) with
| {steps = steps; tcenv = tcenv; debug = debug1; delta_level = delta_level; primitive_steps = primitive_steps; strong = strong; memoize_lazy = memoize_lazy; normalize_pure_lets = normalize_pure_lets; reifying = reifying} -> begin
delta_level
end))


let __proj__Mkcfg__item__primitive_steps : cfg  ->  primitive_step FStar_Util.psmap = (fun projectee -> (match (projectee) with
| {steps = steps; tcenv = tcenv; debug = debug1; delta_level = delta_level; primitive_steps = primitive_steps; strong = strong; memoize_lazy = memoize_lazy; normalize_pure_lets = normalize_pure_lets; reifying = reifying} -> begin
primitive_steps
end))


let __proj__Mkcfg__item__strong : cfg  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {steps = steps; tcenv = tcenv; debug = debug1; delta_level = delta_level; primitive_steps = primitive_steps; strong = strong; memoize_lazy = memoize_lazy; normalize_pure_lets = normalize_pure_lets; reifying = reifying} -> begin
strong
end))


let __proj__Mkcfg__item__memoize_lazy : cfg  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {steps = steps; tcenv = tcenv; debug = debug1; delta_level = delta_level; primitive_steps = primitive_steps; strong = strong; memoize_lazy = memoize_lazy; normalize_pure_lets = normalize_pure_lets; reifying = reifying} -> begin
memoize_lazy
end))


let __proj__Mkcfg__item__normalize_pure_lets : cfg  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {steps = steps; tcenv = tcenv; debug = debug1; delta_level = delta_level; primitive_steps = primitive_steps; strong = strong; memoize_lazy = memoize_lazy; normalize_pure_lets = normalize_pure_lets; reifying = reifying} -> begin
normalize_pure_lets
end))


let __proj__Mkcfg__item__reifying : cfg  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {steps = steps; tcenv = tcenv; debug = debug1; delta_level = delta_level; primitive_steps = primitive_steps; strong = strong; memoize_lazy = memoize_lazy; normalize_pure_lets = normalize_pure_lets; reifying = reifying} -> begin
reifying
end))


let cfg_to_string : cfg  ->  Prims.string = (fun cfg -> (

let uu____2460 = (

let uu____2463 = (

let uu____2466 = (

let uu____2467 = (steps_to_string cfg.steps)
in (FStar_Util.format1 "  steps = %s" uu____2467))
in (uu____2466)::("}")::[])
in ("{")::uu____2463)
in (FStar_String.concat "\n" uu____2460)))


let cfg_env : cfg  ->  FStar_TypeChecker_Env.env = (fun cfg -> cfg.tcenv)


let add_steps : primitive_step FStar_Util.psmap  ->  primitive_step Prims.list  ->  primitive_step FStar_Util.psmap = (fun m l -> (FStar_List.fold_right (fun p m1 -> (

let uu____2504 = (FStar_Ident.text_of_lid p.name)
in (FStar_Util.psmap_add m1 uu____2504 p))) l m))


let prim_from_list : primitive_step Prims.list  ->  primitive_step FStar_Util.psmap = (fun l -> (

let uu____2518 = (FStar_Util.psmap_empty ())
in (add_steps uu____2518 l)))


let find_prim_step : cfg  ->  FStar_Syntax_Syntax.fv  ->  primitive_step FStar_Pervasives_Native.option = (fun cfg fv -> (

let uu____2533 = (FStar_Ident.text_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.psmap_try_find cfg.primitive_steps uu____2533)))


let is_prim_step : cfg  ->  FStar_Syntax_Syntax.fv  ->  Prims.bool = (fun cfg fv -> (

let uu____2544 = (

let uu____2547 = (FStar_Ident.text_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.psmap_try_find cfg.primitive_steps uu____2547))
in (FStar_Util.is_some uu____2544)))


let log : cfg  ->  (unit  ->  unit)  ->  unit = (fun cfg f -> (match (cfg.debug.gen) with
| true -> begin
(f ())
end
| uu____2563 -> begin
()
end))


let log_top : cfg  ->  (unit  ->  unit)  ->  unit = (fun cfg f -> (match (cfg.debug.top) with
| true -> begin
(f ())
end
| uu____2579 -> begin
()
end))


let log_cfg : cfg  ->  (unit  ->  unit)  ->  unit = (fun cfg f -> (match (cfg.debug.cfg) with
| true -> begin
(f ())
end
| uu____2595 -> begin
()
end))


let log_primops : cfg  ->  (unit  ->  unit)  ->  unit = (fun cfg f -> (match (cfg.debug.primop) with
| true -> begin
(f ())
end
| uu____2611 -> begin
()
end))


let log_unfolding : cfg  ->  (unit  ->  unit)  ->  unit = (fun cfg f -> (match (cfg.debug.unfolding) with
| true -> begin
(f ())
end
| uu____2627 -> begin
()
end))


let log_nbe : cfg  ->  (unit  ->  unit)  ->  unit = (fun cfg f -> (

let uu____2643 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("NBE")))
in (match (uu____2643) with
| true -> begin
(f ())
end
| uu____2644 -> begin
()
end)))


let embed_simple : 'a . 'a FStar_Syntax_Embeddings.embedding  ->  FStar_Range.range  ->  'a  ->  FStar_Syntax_Syntax.term = (fun emb r x -> (

let uu____2673 = (FStar_Syntax_Embeddings.embed emb x)
in (uu____2673 r FStar_Pervasives_Native.None FStar_Syntax_Embeddings.id_norm_cb)))


let try_unembed_simple : 'a . 'a FStar_Syntax_Embeddings.embedding  ->  FStar_Syntax_Syntax.term  ->  'a FStar_Pervasives_Native.option = (fun emb x -> (

let uu____2728 = (FStar_Syntax_Embeddings.unembed emb x)
in (uu____2728 false FStar_Syntax_Embeddings.id_norm_cb)))


let mk : 'Auu____2745 . 'Auu____2745  ->  FStar_Range.range  ->  'Auu____2745 FStar_Syntax_Syntax.syntax = (fun t r -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r))


let built_in_primitive_steps : primitive_step FStar_Util.psmap = (

let arg_as_int1 = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (try_unembed_simple FStar_Syntax_Embeddings.e_int)))
in (

let arg_as_bool1 = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (try_unembed_simple FStar_Syntax_Embeddings.e_bool)))
in (

let arg_as_char1 = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (try_unembed_simple FStar_Syntax_Embeddings.e_char)))
in (

let arg_as_string1 = (fun a -> (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (try_unembed_simple FStar_Syntax_Embeddings.e_string)))
in (

let arg_as_list1 = (fun e a -> (

let uu____2859 = (

let uu____2868 = (FStar_Syntax_Embeddings.e_list e)
in (try_unembed_simple uu____2868))
in (FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____2859)))
in (

let arg_as_bounded_int1 = (fun uu____2898 -> (match (uu____2898) with
| (a, uu____2912) -> begin
(

let uu____2923 = (FStar_Syntax_Util.head_and_args' a)
in (match (uu____2923) with
| (hd1, args) -> begin
(

let a1 = (FStar_Syntax_Util.unlazy_emb a)
in (

let uu____2967 = (

let uu____2982 = (

let uu____2983 = (FStar_Syntax_Subst.compress hd1)
in uu____2983.FStar_Syntax_Syntax.n)
in ((uu____2982), (args)))
in (match (uu____2967) with
| (FStar_Syntax_Syntax.Tm_fvar (fv1), ((arg, uu____3004))::[]) when (

let uu____3039 = (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.ends_with uu____3039 "int_to_t")) -> begin
(

let arg1 = (FStar_Syntax_Util.unlazy_emb arg)
in (

let uu____3041 = (

let uu____3042 = (FStar_Syntax_Subst.compress arg1)
in uu____3042.FStar_Syntax_Syntax.n)
in (match (uu____3041) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, FStar_Pervasives_Native.None)) -> begin
(

let uu____3062 = (

let uu____3067 = (FStar_BigInt.big_int_of_string i)
in ((fv1), (uu____3067)))
in FStar_Pervasives_Native.Some (uu____3062))
end
| uu____3072 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____3077 -> begin
FStar_Pervasives_Native.None
end)))
end))
end))
in (

let lift_unary = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a))::[] -> begin
(

let uu____3139 = (f a)
in FStar_Pervasives_Native.Some (uu____3139))
end
| uu____3140 -> begin
FStar_Pervasives_Native.None
end))
in (

let lift_binary = (fun f aopts -> (match (aopts) with
| (FStar_Pervasives_Native.Some (a0))::(FStar_Pervasives_Native.Some (a1))::[] -> begin
(

let uu____3196 = (f a0 a1)
in FStar_Pervasives_Native.Some (uu____3196))
end
| uu____3197 -> begin
FStar_Pervasives_Native.None
end))
in (

let unary_op1 = (fun as_a f res norm_cb args -> (

let uu____3266 = (FStar_List.map as_a args)
in (lift_unary (f res.psc_range) uu____3266)))
in (

let binary_op1 = (fun as_a f res n1 args -> (

let uu____3350 = (FStar_List.map as_a args)
in (lift_binary (f res.psc_range) uu____3350)))
in (

let as_primitive_step = (fun is_strong uu____3403 -> (match (uu____3403) with
| (l, arity, u_arity, f, f_nbe) -> begin
{name = l; arity = arity; univ_arity = u_arity; auto_reflect = FStar_Pervasives_Native.None; strong_reduction_ok = is_strong; requires_binder_substitution = false; interpretation = f; interpretation_nbe = (fun _cb -> f_nbe)}
end))
in (

let unary_int_op1 = (fun f -> (unary_op1 arg_as_int1 (fun r x -> (

let uu____3506 = (f x)
in (embed_simple FStar_Syntax_Embeddings.e_int r uu____3506)))))
in (

let binary_int_op1 = (fun f -> (binary_op1 arg_as_int1 (fun r x y -> (

let uu____3549 = (f x y)
in (embed_simple FStar_Syntax_Embeddings.e_int r uu____3549)))))
in (

let unary_bool_op1 = (fun f -> (unary_op1 arg_as_bool1 (fun r x -> (

let uu____3585 = (f x)
in (embed_simple FStar_Syntax_Embeddings.e_bool r uu____3585)))))
in (

let binary_bool_op1 = (fun f -> (binary_op1 arg_as_bool1 (fun r x y -> (

let uu____3628 = (f x y)
in (embed_simple FStar_Syntax_Embeddings.e_bool r uu____3628)))))
in (

let binary_string_op1 = (fun f -> (binary_op1 arg_as_string1 (fun r x y -> (

let uu____3671 = (f x y)
in (embed_simple FStar_Syntax_Embeddings.e_string r uu____3671)))))
in (

let mixed_binary_op1 = (fun as_a as_b embed_c f res _norm_cb args -> (match (args) with
| (a)::(b)::[] -> begin
(

let uu____3824 = (

let uu____3833 = (as_a a)
in (

let uu____3836 = (as_b b)
in ((uu____3833), (uu____3836))))
in (match (uu____3824) with
| (FStar_Pervasives_Native.Some (a1), FStar_Pervasives_Native.Some (b1)) -> begin
(

let uu____3851 = (

let uu____3852 = (f res.psc_range a1 b1)
in (embed_c res.psc_range uu____3852))
in FStar_Pervasives_Native.Some (uu____3851))
end
| uu____3853 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____3862 -> begin
FStar_Pervasives_Native.None
end))
in (

let list_of_string'1 = (fun rng s -> (

let name = (fun l -> (

let uu____3882 = (

let uu____3883 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____3883))
in (mk uu____3882 rng)))
in (

let char_t = (name FStar_Parser_Const.char_lid)
in (

let charterm = (fun c -> (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))) rng))
in (

let uu____3897 = (

let uu____3900 = (FStar_String.list_of_string s)
in (FStar_List.map charterm uu____3900))
in (FStar_All.pipe_left (FStar_Syntax_Util.mk_list char_t rng) uu____3897))))))
in (

let string_of_list'1 = (fun rng l -> (

let s = (FStar_String.string_of_list l)
in (FStar_Syntax_Util.exp_string s)))
in (

let string_compare'1 = (fun rng s1 s2 -> (

let r = (FStar_String.compare s1 s2)
in (

let uu____3942 = (

let uu____3943 = (FStar_Util.string_of_int r)
in (FStar_BigInt.big_int_of_string uu____3943))
in (embed_simple FStar_Syntax_Embeddings.e_int rng uu____3942))))
in (

let string_concat'1 = (fun psc _n args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____4030 = (arg_as_string1 a1)
in (match (uu____4030) with
| FStar_Pervasives_Native.Some (s1) -> begin
(

let uu____4036 = (arg_as_list1 FStar_Syntax_Embeddings.e_string a2)
in (match (uu____4036) with
| FStar_Pervasives_Native.Some (s2) -> begin
(

let r = (FStar_String.concat s1 s2)
in (

let uu____4049 = (embed_simple FStar_Syntax_Embeddings.e_string psc.psc_range r)
in FStar_Pervasives_Native.Some (uu____4049)))
end
| uu____4050 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4055 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4058 -> begin
FStar_Pervasives_Native.None
end))
in (

let string_split'1 = (fun psc _norm_cb args -> (match (args) with
| (a1)::(a2)::[] -> begin
(

let uu____4141 = (arg_as_list1 FStar_Syntax_Embeddings.e_char a1)
in (match (uu____4141) with
| FStar_Pervasives_Native.Some (s1) -> begin
(

let uu____4157 = (arg_as_string1 a2)
in (match (uu____4157) with
| FStar_Pervasives_Native.Some (s2) -> begin
(

let r = (FStar_String.split s1 s2)
in (

let uu____4166 = (

let uu____4167 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string)
in (embed_simple uu____4167 psc.psc_range r))
in FStar_Pervasives_Native.Some (uu____4166)))
end
| uu____4174 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4177 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4183 -> begin
FStar_Pervasives_Native.None
end))
in (

let string_substring'1 = (fun psc _norm_cb args -> (match (args) with
| (a1)::(a2)::(a3)::[] -> begin
(

let uu____4223 = (

let uu____4236 = (arg_as_string1 a1)
in (

let uu____4239 = (arg_as_int1 a2)
in (

let uu____4242 = (arg_as_int1 a3)
in ((uu____4236), (uu____4239), (uu____4242)))))
in (match (uu____4223) with
| (FStar_Pervasives_Native.Some (s1), FStar_Pervasives_Native.Some (n1), FStar_Pervasives_Native.Some (n2)) -> begin
(

let n11 = (FStar_BigInt.to_int_fs n1)
in (

let n21 = (FStar_BigInt.to_int_fs n2)
in (FStar_All.try_with (fun uu___266_4269 -> (match (()) with
| () -> begin
(

let r = (FStar_String.substring s1 n11 n21)
in (

let uu____4273 = (embed_simple FStar_Syntax_Embeddings.e_string psc.psc_range r)
in FStar_Pervasives_Native.Some (uu____4273)))
end)) (fun uu___265_4275 -> FStar_Pervasives_Native.None))))
end
| uu____4278 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4291 -> begin
FStar_Pervasives_Native.None
end))
in (

let string_of_int1 = (fun rng i -> (

let uu____4305 = (FStar_BigInt.string_of_big_int i)
in (embed_simple FStar_Syntax_Embeddings.e_string rng uu____4305)))
in (

let string_of_bool1 = (fun rng b -> (embed_simple FStar_Syntax_Embeddings.e_string rng (match (b) with
| true -> begin
"true"
end
| uu____4317 -> begin
"false"
end)))
in (

let mk_range1 = (fun psc _norm_cb args -> (match (args) with
| (fn)::(from_line)::(from_col)::(to_line)::(to_col)::[] -> begin
(

let uu____4351 = (

let uu____4372 = (arg_as_string1 fn)
in (

let uu____4375 = (arg_as_int1 from_line)
in (

let uu____4378 = (arg_as_int1 from_col)
in (

let uu____4381 = (arg_as_int1 to_line)
in (

let uu____4384 = (arg_as_int1 to_col)
in ((uu____4372), (uu____4375), (uu____4378), (uu____4381), (uu____4384)))))))
in (match (uu____4351) with
| (FStar_Pervasives_Native.Some (fn1), FStar_Pervasives_Native.Some (from_l), FStar_Pervasives_Native.Some (from_c), FStar_Pervasives_Native.Some (to_l), FStar_Pervasives_Native.Some (to_c)) -> begin
(

let r = (

let uu____4415 = (

let uu____4416 = (FStar_BigInt.to_int_fs from_l)
in (

let uu____4417 = (FStar_BigInt.to_int_fs from_c)
in (FStar_Range.mk_pos uu____4416 uu____4417)))
in (

let uu____4418 = (

let uu____4419 = (FStar_BigInt.to_int_fs to_l)
in (

let uu____4420 = (FStar_BigInt.to_int_fs to_c)
in (FStar_Range.mk_pos uu____4419 uu____4420)))
in (FStar_Range.mk_range fn1 uu____4415 uu____4418)))
in (

let uu____4421 = (embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r)
in FStar_Pervasives_Native.Some (uu____4421)))
end
| uu____4422 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4443 -> begin
FStar_Pervasives_Native.None
end))
in (

let decidable_eq1 = (fun neg psc _norm_cb args -> (

let r = psc.psc_range
in (

let tru = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) r)
in (

let fal = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) r)
in (match (args) with
| ((_typ, uu____4485))::((a1, uu____4487))::((a2, uu____4489))::[] -> begin
(

let uu____4546 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____4546) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
fal
end
| uu____4549 -> begin
tru
end))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((match (neg) with
| true -> begin
tru
end
| uu____4550 -> begin
fal
end))
end
| uu____4551 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4552 -> begin
(failwith "Unexpected number of arguments")
end)))))
in (

let prims_to_fstar_range_step1 = (fun psc _norm_cb args -> (match (args) with
| ((a1, uu____4596))::[] -> begin
(

let uu____4613 = (try_unembed_simple FStar_Syntax_Embeddings.e_range a1)
in (match (uu____4613) with
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____4619 = (embed_simple FStar_Syntax_Embeddings.e_range psc.psc_range r)
in FStar_Pervasives_Native.Some (uu____4619))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____4620 -> begin
(failwith "Unexpected number of arguments")
end))
in (

let bogus_cbs = {FStar_TypeChecker_NBETerm.iapp = (fun h _args -> h); FStar_TypeChecker_NBETerm.translate = (fun uu____4639 -> (failwith "bogus_cbs translate"))}
in (

let basic_ops = (

let uu____4671 = (

let uu____4700 = (FStar_TypeChecker_NBETerm.unary_int_op (fun x -> (FStar_BigInt.minus_big_int x)))
in ((FStar_Parser_Const.op_Minus), ((Prims.parse_int "1")), ((Prims.parse_int "0")), ((unary_int_op1 (fun x -> (FStar_BigInt.minus_big_int x)))), (uu____4700)))
in (

let uu____4731 = (

let uu____4762 = (

let uu____4791 = (FStar_TypeChecker_NBETerm.binary_int_op (fun x y -> (FStar_BigInt.add_big_int x y)))
in ((FStar_Parser_Const.op_Addition), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_int_op1 (fun x y -> (FStar_BigInt.add_big_int x y)))), (uu____4791)))
in (

let uu____4828 = (

let uu____4859 = (

let uu____4888 = (FStar_TypeChecker_NBETerm.binary_int_op (fun x y -> (FStar_BigInt.sub_big_int x y)))
in ((FStar_Parser_Const.op_Subtraction), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_int_op1 (fun x y -> (FStar_BigInt.sub_big_int x y)))), (uu____4888)))
in (

let uu____4925 = (

let uu____4956 = (

let uu____4985 = (FStar_TypeChecker_NBETerm.binary_int_op (fun x y -> (FStar_BigInt.mult_big_int x y)))
in ((FStar_Parser_Const.op_Multiply), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_int_op1 (fun x y -> (FStar_BigInt.mult_big_int x y)))), (uu____4985)))
in (

let uu____5022 = (

let uu____5053 = (

let uu____5082 = (FStar_TypeChecker_NBETerm.binary_int_op (fun x y -> (FStar_BigInt.div_big_int x y)))
in ((FStar_Parser_Const.op_Division), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_int_op1 (fun x y -> (FStar_BigInt.div_big_int x y)))), (uu____5082)))
in (

let uu____5119 = (

let uu____5150 = (

let uu____5179 = (FStar_TypeChecker_NBETerm.binary_op FStar_TypeChecker_NBETerm.arg_as_int (fun x y -> (

let uu____5191 = (FStar_BigInt.lt_big_int x y)
in (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_bool bogus_cbs uu____5191))))
in ((FStar_Parser_Const.op_LT), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_op1 arg_as_int1 (fun r x y -> (

let uu____5217 = (FStar_BigInt.lt_big_int x y)
in (embed_simple FStar_Syntax_Embeddings.e_bool r uu____5217))))), (uu____5179)))
in (

let uu____5218 = (

let uu____5249 = (

let uu____5278 = (FStar_TypeChecker_NBETerm.binary_op FStar_TypeChecker_NBETerm.arg_as_int (fun x y -> (

let uu____5290 = (FStar_BigInt.le_big_int x y)
in (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_bool bogus_cbs uu____5290))))
in ((FStar_Parser_Const.op_LTE), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_op1 arg_as_int1 (fun r x y -> (

let uu____5316 = (FStar_BigInt.le_big_int x y)
in (embed_simple FStar_Syntax_Embeddings.e_bool r uu____5316))))), (uu____5278)))
in (

let uu____5317 = (

let uu____5348 = (

let uu____5377 = (FStar_TypeChecker_NBETerm.binary_op FStar_TypeChecker_NBETerm.arg_as_int (fun x y -> (

let uu____5389 = (FStar_BigInt.gt_big_int x y)
in (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_bool bogus_cbs uu____5389))))
in ((FStar_Parser_Const.op_GT), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_op1 arg_as_int1 (fun r x y -> (

let uu____5415 = (FStar_BigInt.gt_big_int x y)
in (embed_simple FStar_Syntax_Embeddings.e_bool r uu____5415))))), (uu____5377)))
in (

let uu____5416 = (

let uu____5447 = (

let uu____5476 = (FStar_TypeChecker_NBETerm.binary_op FStar_TypeChecker_NBETerm.arg_as_int (fun x y -> (

let uu____5488 = (FStar_BigInt.ge_big_int x y)
in (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_bool bogus_cbs uu____5488))))
in ((FStar_Parser_Const.op_GTE), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_op1 arg_as_int1 (fun r x y -> (

let uu____5514 = (FStar_BigInt.ge_big_int x y)
in (embed_simple FStar_Syntax_Embeddings.e_bool r uu____5514))))), (uu____5476)))
in (

let uu____5515 = (

let uu____5546 = (

let uu____5575 = (FStar_TypeChecker_NBETerm.binary_int_op (fun x y -> (FStar_BigInt.mod_big_int x y)))
in ((FStar_Parser_Const.op_Modulus), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_int_op1 (fun x y -> (FStar_BigInt.mod_big_int x y)))), (uu____5575)))
in (

let uu____5612 = (

let uu____5643 = (

let uu____5672 = (FStar_TypeChecker_NBETerm.unary_bool_op (fun x -> (not (x))))
in ((FStar_Parser_Const.op_Negation), ((Prims.parse_int "1")), ((Prims.parse_int "0")), ((unary_bool_op1 (fun x -> (not (x))))), (uu____5672)))
in (

let uu____5703 = (

let uu____5734 = (

let uu____5763 = (FStar_TypeChecker_NBETerm.binary_bool_op (fun x y -> (x && y)))
in ((FStar_Parser_Const.op_And), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_bool_op1 (fun x y -> (x && y)))), (uu____5763)))
in (

let uu____5800 = (

let uu____5831 = (

let uu____5860 = (FStar_TypeChecker_NBETerm.binary_bool_op (fun x y -> (x || y)))
in ((FStar_Parser_Const.op_Or), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_bool_op1 (fun x y -> (x || y)))), (uu____5860)))
in (

let uu____5897 = (

let uu____5928 = (

let uu____5957 = (FStar_TypeChecker_NBETerm.binary_string_op (fun x y -> (Prims.strcat x y)))
in ((FStar_Parser_Const.strcat_lid), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_string_op1 (fun x y -> (Prims.strcat x y)))), (uu____5957)))
in (

let uu____5994 = (

let uu____6025 = (

let uu____6054 = (FStar_TypeChecker_NBETerm.binary_string_op (fun x y -> (Prims.strcat x y)))
in ((FStar_Parser_Const.strcat_lid'), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_string_op1 (fun x y -> (Prims.strcat x y)))), (uu____6054)))
in (

let uu____6091 = (

let uu____6122 = (

let uu____6153 = (

let uu____6182 = (FStar_TypeChecker_NBETerm.unary_op FStar_TypeChecker_NBETerm.arg_as_int FStar_TypeChecker_NBETerm.string_of_int)
in ((FStar_Parser_Const.string_of_int_lid), ((Prims.parse_int "1")), ((Prims.parse_int "0")), ((unary_op1 arg_as_int1 string_of_int1)), (uu____6182)))
in (

let uu____6207 = (

let uu____6238 = (

let uu____6267 = (FStar_TypeChecker_NBETerm.unary_op FStar_TypeChecker_NBETerm.arg_as_bool FStar_TypeChecker_NBETerm.string_of_bool)
in ((FStar_Parser_Const.string_of_bool_lid), ((Prims.parse_int "1")), ((Prims.parse_int "0")), ((unary_op1 arg_as_bool1 string_of_bool1)), (uu____6267)))
in (

let uu____6292 = (

let uu____6323 = (

let uu____6352 = (FStar_TypeChecker_NBETerm.binary_op FStar_TypeChecker_NBETerm.arg_as_string FStar_TypeChecker_NBETerm.string_compare')
in ((FStar_Parser_Const.string_compare), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_op1 arg_as_string1 string_compare'1)), (uu____6352)))
in (

let uu____6377 = (

let uu____6408 = (

let uu____6439 = (

let uu____6470 = (

let uu____6499 = (FStar_Parser_Const.p2l (("FStar")::("String")::("list_of_string")::[]))
in (

let uu____6500 = (FStar_TypeChecker_NBETerm.unary_op FStar_TypeChecker_NBETerm.arg_as_string FStar_TypeChecker_NBETerm.list_of_string')
in ((uu____6499), ((Prims.parse_int "1")), ((Prims.parse_int "0")), ((unary_op1 arg_as_string1 list_of_string'1)), (uu____6500))))
in (

let uu____6525 = (

let uu____6556 = (

let uu____6585 = (FStar_Parser_Const.p2l (("FStar")::("String")::("string_of_list")::[]))
in (

let uu____6586 = (FStar_TypeChecker_NBETerm.unary_op (FStar_TypeChecker_NBETerm.arg_as_list FStar_TypeChecker_NBETerm.e_char) FStar_TypeChecker_NBETerm.string_of_list')
in ((uu____6585), ((Prims.parse_int "1")), ((Prims.parse_int "0")), ((unary_op1 (arg_as_list1 FStar_Syntax_Embeddings.e_char) string_of_list'1)), (uu____6586))))
in (

let uu____6619 = (

let uu____6650 = (

let uu____6679 = (FStar_Parser_Const.p2l (("FStar")::("String")::("split")::[]))
in ((uu____6679), ((Prims.parse_int "2")), ((Prims.parse_int "0")), (string_split'1), (FStar_TypeChecker_NBETerm.string_split')))
in (

let uu____6698 = (

let uu____6729 = (

let uu____6758 = (FStar_Parser_Const.p2l (("FStar")::("String")::("substring")::[]))
in ((uu____6758), ((Prims.parse_int "3")), ((Prims.parse_int "0")), (string_substring'1), (FStar_TypeChecker_NBETerm.string_substring')))
in (

let uu____6777 = (

let uu____6808 = (

let uu____6837 = (FStar_Parser_Const.p2l (("FStar")::("String")::("concat")::[]))
in ((uu____6837), ((Prims.parse_int "2")), ((Prims.parse_int "0")), (string_concat'1), (FStar_TypeChecker_NBETerm.string_concat')))
in (

let uu____6856 = (

let uu____6887 = (

let uu____6916 = (FStar_Parser_Const.p2l (("Prims")::("mk_range")::[]))
in ((uu____6916), ((Prims.parse_int "5")), ((Prims.parse_int "0")), (mk_range1), (FStar_TypeChecker_NBETerm.mk_range)))
in (

let uu____6935 = (

let uu____6966 = (

let uu____6995 = (FStar_Parser_Const.p2l (("FStar")::("Range")::("prims_to_fstar_range")::[]))
in ((uu____6995), ((Prims.parse_int "1")), ((Prims.parse_int "0")), (prims_to_fstar_range_step1), (FStar_TypeChecker_NBETerm.prims_to_fstar_range_step)))
in (uu____6966)::[])
in (uu____6887)::uu____6935))
in (uu____6808)::uu____6856))
in (uu____6729)::uu____6777))
in (uu____6650)::uu____6698))
in (uu____6556)::uu____6619))
in (uu____6470)::uu____6525))
in (((FStar_Parser_Const.op_notEq), ((Prims.parse_int "3")), ((Prims.parse_int "0")), ((decidable_eq1 true)), ((FStar_TypeChecker_NBETerm.decidable_eq true))))::uu____6439)
in (((FStar_Parser_Const.op_Eq), ((Prims.parse_int "3")), ((Prims.parse_int "0")), ((decidable_eq1 false)), ((FStar_TypeChecker_NBETerm.decidable_eq false))))::uu____6408)
in (uu____6323)::uu____6377))
in (uu____6238)::uu____6292))
in (uu____6153)::uu____6207))
in (((FStar_Parser_Const.str_make_lid), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((mixed_binary_op1 arg_as_int1 arg_as_char1 (embed_simple FStar_Syntax_Embeddings.e_string) (fun r x y -> (

let uu____7469 = (FStar_BigInt.to_int_fs x)
in (FStar_String.make uu____7469 y))))), ((FStar_TypeChecker_NBETerm.mixed_binary_op FStar_TypeChecker_NBETerm.arg_as_int FStar_TypeChecker_NBETerm.arg_as_char (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string bogus_cbs) (fun x y -> (

let uu____7477 = (FStar_BigInt.to_int_fs x)
in (FStar_String.make uu____7477 y)))))))::uu____6122)
in (uu____6025)::uu____6091))
in (uu____5928)::uu____5994))
in (uu____5831)::uu____5897))
in (uu____5734)::uu____5800))
in (uu____5643)::uu____5703))
in (uu____5546)::uu____5612))
in (uu____5447)::uu____5515))
in (uu____5348)::uu____5416))
in (uu____5249)::uu____5317))
in (uu____5150)::uu____5218))
in (uu____5053)::uu____5119))
in (uu____4956)::uu____5022))
in (uu____4859)::uu____4925))
in (uu____4762)::uu____4828))
in (uu____4671)::uu____4731))
in (

let weak_ops = []
in (

let bounded_arith_ops = (

let bounded_signed_int_types = ("Int8")::("Int16")::("Int32")::("Int64")::[]
in (

let bounded_unsigned_int_types = ("UInt8")::("UInt16")::("UInt32")::("UInt64")::("UInt128")::[]
in (

let int_as_bounded1 = (fun r int_to_t1 n1 -> (

let c = (embed_simple FStar_Syntax_Embeddings.e_int r n1)
in (

let int_to_t2 = (FStar_Syntax_Syntax.fv_to_tm int_to_t1)
in (

let uu____8014 = (

let uu____8019 = (

let uu____8020 = (FStar_Syntax_Syntax.as_arg c)
in (uu____8020)::[])
in (FStar_Syntax_Syntax.mk_Tm_app int_to_t2 uu____8019))
in (uu____8014 FStar_Pervasives_Native.None r)))))
in (

let add_sub_mul_v = (FStar_All.pipe_right (FStar_List.append bounded_signed_int_types bounded_unsigned_int_types) (FStar_List.collect (fun m -> (

let uu____8142 = (

let uu____8171 = (FStar_Parser_Const.p2l (("FStar")::(m)::("add")::[]))
in (

let uu____8172 = (FStar_TypeChecker_NBETerm.binary_op FStar_TypeChecker_NBETerm.arg_as_bounded_int (fun uu____8190 uu____8191 -> (match (((uu____8190), (uu____8191))) with
| ((int_to_t1, x), (uu____8210, y)) -> begin
(

let uu____8220 = (FStar_BigInt.add_big_int x y)
in (FStar_TypeChecker_NBETerm.int_as_bounded int_to_t1 uu____8220))
end)))
in ((uu____8171), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_op1 arg_as_bounded_int1 (fun r uu____8252 uu____8253 -> (match (((uu____8252), (uu____8253))) with
| ((int_to_t1, x), (uu____8272, y)) -> begin
(

let uu____8282 = (FStar_BigInt.add_big_int x y)
in (int_as_bounded1 r int_to_t1 uu____8282))
end)))), (uu____8172))))
in (

let uu____8283 = (

let uu____8314 = (

let uu____8343 = (FStar_Parser_Const.p2l (("FStar")::(m)::("sub")::[]))
in (

let uu____8344 = (FStar_TypeChecker_NBETerm.binary_op FStar_TypeChecker_NBETerm.arg_as_bounded_int (fun uu____8362 uu____8363 -> (match (((uu____8362), (uu____8363))) with
| ((int_to_t1, x), (uu____8382, y)) -> begin
(

let uu____8392 = (FStar_BigInt.sub_big_int x y)
in (FStar_TypeChecker_NBETerm.int_as_bounded int_to_t1 uu____8392))
end)))
in ((uu____8343), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_op1 arg_as_bounded_int1 (fun r uu____8424 uu____8425 -> (match (((uu____8424), (uu____8425))) with
| ((int_to_t1, x), (uu____8444, y)) -> begin
(

let uu____8454 = (FStar_BigInt.sub_big_int x y)
in (int_as_bounded1 r int_to_t1 uu____8454))
end)))), (uu____8344))))
in (

let uu____8455 = (

let uu____8486 = (

let uu____8515 = (FStar_Parser_Const.p2l (("FStar")::(m)::("mul")::[]))
in (

let uu____8516 = (FStar_TypeChecker_NBETerm.binary_op FStar_TypeChecker_NBETerm.arg_as_bounded_int (fun uu____8534 uu____8535 -> (match (((uu____8534), (uu____8535))) with
| ((int_to_t1, x), (uu____8554, y)) -> begin
(

let uu____8564 = (FStar_BigInt.mult_big_int x y)
in (FStar_TypeChecker_NBETerm.int_as_bounded int_to_t1 uu____8564))
end)))
in ((uu____8515), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_op1 arg_as_bounded_int1 (fun r uu____8596 uu____8597 -> (match (((uu____8596), (uu____8597))) with
| ((int_to_t1, x), (uu____8616, y)) -> begin
(

let uu____8626 = (FStar_BigInt.mult_big_int x y)
in (int_as_bounded1 r int_to_t1 uu____8626))
end)))), (uu____8516))))
in (

let uu____8627 = (

let uu____8658 = (

let uu____8687 = (FStar_Parser_Const.p2l (("FStar")::(m)::("v")::[]))
in (

let uu____8688 = (FStar_TypeChecker_NBETerm.unary_op FStar_TypeChecker_NBETerm.arg_as_bounded_int (fun uu____8702 -> (match (uu____8702) with
| (int_to_t1, x) -> begin
(FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int bogus_cbs x)
end)))
in ((uu____8687), ((Prims.parse_int "1")), ((Prims.parse_int "0")), ((unary_op1 arg_as_bounded_int1 (fun r uu____8736 -> (match (uu____8736) with
| (int_to_t1, x) -> begin
(embed_simple FStar_Syntax_Embeddings.e_int r x)
end)))), (uu____8688))))
in (uu____8658)::[])
in (uu____8486)::uu____8627))
in (uu____8314)::uu____8455))
in (uu____8142)::uu____8283)))))
in (

let div_mod_unsigned = (FStar_All.pipe_right bounded_unsigned_int_types (FStar_List.collect (fun m -> (

let uu____8978 = (

let uu____9007 = (FStar_Parser_Const.p2l (("FStar")::(m)::("div")::[]))
in (

let uu____9008 = (FStar_TypeChecker_NBETerm.binary_op FStar_TypeChecker_NBETerm.arg_as_bounded_int (fun uu____9026 uu____9027 -> (match (((uu____9026), (uu____9027))) with
| ((int_to_t1, x), (uu____9046, y)) -> begin
(

let uu____9056 = (FStar_BigInt.div_big_int x y)
in (FStar_TypeChecker_NBETerm.int_as_bounded int_to_t1 uu____9056))
end)))
in ((uu____9007), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_op1 arg_as_bounded_int1 (fun r uu____9088 uu____9089 -> (match (((uu____9088), (uu____9089))) with
| ((int_to_t1, x), (uu____9108, y)) -> begin
(

let uu____9118 = (FStar_BigInt.div_big_int x y)
in (int_as_bounded1 r int_to_t1 uu____9118))
end)))), (uu____9008))))
in (

let uu____9119 = (

let uu____9150 = (

let uu____9179 = (FStar_Parser_Const.p2l (("FStar")::(m)::("rem")::[]))
in (

let uu____9180 = (FStar_TypeChecker_NBETerm.binary_op FStar_TypeChecker_NBETerm.arg_as_bounded_int (fun uu____9198 uu____9199 -> (match (((uu____9198), (uu____9199))) with
| ((int_to_t1, x), (uu____9218, y)) -> begin
(

let uu____9228 = (FStar_BigInt.mod_big_int x y)
in (FStar_TypeChecker_NBETerm.int_as_bounded int_to_t1 uu____9228))
end)))
in ((uu____9179), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_op1 arg_as_bounded_int1 (fun r uu____9260 uu____9261 -> (match (((uu____9260), (uu____9261))) with
| ((int_to_t1, x), (uu____9280, y)) -> begin
(

let uu____9290 = (FStar_BigInt.mod_big_int x y)
in (int_as_bounded1 r int_to_t1 uu____9290))
end)))), (uu____9180))))
in (uu____9150)::[])
in (uu____8978)::uu____9119)))))
in (

let mask = (fun m -> (match (m) with
| "UInt8" -> begin
(FStar_BigInt.of_hex "ff")
end
| "UInt16" -> begin
(FStar_BigInt.of_hex "ffff")
end
| "UInt32" -> begin
(FStar_BigInt.of_hex "ffffffff")
end
| "UInt64" -> begin
(FStar_BigInt.of_hex "ffffffffffffffff")
end
| "UInt128" -> begin
(FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff")
end
| uu____9381 -> begin
(

let uu____9382 = (FStar_Util.format1 "Impossible: bad string on mask: %s\n" m)
in (failwith uu____9382))
end))
in (

let bitwise = (FStar_All.pipe_right bounded_unsigned_int_types (FStar_List.collect (fun m -> (

let uu____9478 = (

let uu____9507 = (FStar_Parser_Const.p2l (("FStar")::(m)::("logor")::[]))
in (

let uu____9508 = (FStar_TypeChecker_NBETerm.binary_op FStar_TypeChecker_NBETerm.arg_as_bounded_int (fun uu____9526 uu____9527 -> (match (((uu____9526), (uu____9527))) with
| ((int_to_t1, x), (uu____9546, y)) -> begin
(

let uu____9556 = (FStar_BigInt.logor_big_int x y)
in (FStar_TypeChecker_NBETerm.int_as_bounded int_to_t1 uu____9556))
end)))
in ((uu____9507), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_op1 arg_as_bounded_int1 (fun r uu____9588 uu____9589 -> (match (((uu____9588), (uu____9589))) with
| ((int_to_t1, x), (uu____9608, y)) -> begin
(

let uu____9618 = (FStar_BigInt.logor_big_int x y)
in (int_as_bounded1 r int_to_t1 uu____9618))
end)))), (uu____9508))))
in (

let uu____9619 = (

let uu____9650 = (

let uu____9679 = (FStar_Parser_Const.p2l (("FStar")::(m)::("logand")::[]))
in (

let uu____9680 = (FStar_TypeChecker_NBETerm.binary_op FStar_TypeChecker_NBETerm.arg_as_bounded_int (fun uu____9698 uu____9699 -> (match (((uu____9698), (uu____9699))) with
| ((int_to_t1, x), (uu____9718, y)) -> begin
(

let uu____9728 = (FStar_BigInt.logand_big_int x y)
in (FStar_TypeChecker_NBETerm.int_as_bounded int_to_t1 uu____9728))
end)))
in ((uu____9679), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_op1 arg_as_bounded_int1 (fun r uu____9760 uu____9761 -> (match (((uu____9760), (uu____9761))) with
| ((int_to_t1, x), (uu____9780, y)) -> begin
(

let uu____9790 = (FStar_BigInt.logand_big_int x y)
in (int_as_bounded1 r int_to_t1 uu____9790))
end)))), (uu____9680))))
in (

let uu____9791 = (

let uu____9822 = (

let uu____9851 = (FStar_Parser_Const.p2l (("FStar")::(m)::("logxor")::[]))
in (

let uu____9852 = (FStar_TypeChecker_NBETerm.binary_op FStar_TypeChecker_NBETerm.arg_as_bounded_int (fun uu____9870 uu____9871 -> (match (((uu____9870), (uu____9871))) with
| ((int_to_t1, x), (uu____9890, y)) -> begin
(

let uu____9900 = (FStar_BigInt.logxor_big_int x y)
in (FStar_TypeChecker_NBETerm.int_as_bounded int_to_t1 uu____9900))
end)))
in ((uu____9851), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_op1 arg_as_bounded_int1 (fun r uu____9932 uu____9933 -> (match (((uu____9932), (uu____9933))) with
| ((int_to_t1, x), (uu____9952, y)) -> begin
(

let uu____9962 = (FStar_BigInt.logxor_big_int x y)
in (int_as_bounded1 r int_to_t1 uu____9962))
end)))), (uu____9852))))
in (

let uu____9963 = (

let uu____9994 = (

let uu____10023 = (FStar_Parser_Const.p2l (("FStar")::(m)::("lognot")::[]))
in (

let uu____10024 = (FStar_TypeChecker_NBETerm.unary_op FStar_TypeChecker_NBETerm.arg_as_bounded_int (fun uu____10039 -> (match (uu____10039) with
| (int_to_t1, x) -> begin
(

let uu____10046 = (

let uu____10047 = (FStar_BigInt.lognot_big_int x)
in (

let uu____10048 = (mask m)
in (FStar_BigInt.logand_big_int uu____10047 uu____10048)))
in (FStar_TypeChecker_NBETerm.int_as_bounded int_to_t1 uu____10046))
end)))
in ((uu____10023), ((Prims.parse_int "1")), ((Prims.parse_int "0")), ((unary_op1 arg_as_bounded_int1 (fun r uu____10077 -> (match (uu____10077) with
| (int_to_t1, x) -> begin
(

let uu____10084 = (

let uu____10085 = (FStar_BigInt.lognot_big_int x)
in (

let uu____10086 = (mask m)
in (FStar_BigInt.logand_big_int uu____10085 uu____10086)))
in (int_as_bounded1 r int_to_t1 uu____10084))
end)))), (uu____10024))))
in (

let uu____10087 = (

let uu____10118 = (

let uu____10147 = (FStar_Parser_Const.p2l (("FStar")::(m)::("shift_left")::[]))
in (

let uu____10148 = (FStar_TypeChecker_NBETerm.binary_op FStar_TypeChecker_NBETerm.arg_as_bounded_int (fun uu____10166 uu____10167 -> (match (((uu____10166), (uu____10167))) with
| ((int_to_t1, x), (uu____10186, y)) -> begin
(

let uu____10196 = (

let uu____10197 = (FStar_BigInt.shift_left_big_int x y)
in (

let uu____10198 = (mask m)
in (FStar_BigInt.logand_big_int uu____10197 uu____10198)))
in (FStar_TypeChecker_NBETerm.int_as_bounded int_to_t1 uu____10196))
end)))
in ((uu____10147), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_op1 arg_as_bounded_int1 (fun r uu____10230 uu____10231 -> (match (((uu____10230), (uu____10231))) with
| ((int_to_t1, x), (uu____10250, y)) -> begin
(

let uu____10260 = (

let uu____10261 = (FStar_BigInt.shift_left_big_int x y)
in (

let uu____10262 = (mask m)
in (FStar_BigInt.logand_big_int uu____10261 uu____10262)))
in (int_as_bounded1 r int_to_t1 uu____10260))
end)))), (uu____10148))))
in (

let uu____10263 = (

let uu____10294 = (

let uu____10323 = (FStar_Parser_Const.p2l (("FStar")::(m)::("shift_right")::[]))
in (

let uu____10324 = (FStar_TypeChecker_NBETerm.binary_op FStar_TypeChecker_NBETerm.arg_as_bounded_int (fun uu____10342 uu____10343 -> (match (((uu____10342), (uu____10343))) with
| ((int_to_t1, x), (uu____10362, y)) -> begin
(

let uu____10372 = (FStar_BigInt.shift_right_big_int x y)
in (FStar_TypeChecker_NBETerm.int_as_bounded int_to_t1 uu____10372))
end)))
in ((uu____10323), ((Prims.parse_int "2")), ((Prims.parse_int "0")), ((binary_op1 arg_as_bounded_int1 (fun r uu____10404 uu____10405 -> (match (((uu____10404), (uu____10405))) with
| ((int_to_t1, x), (uu____10424, y)) -> begin
(

let uu____10434 = (FStar_BigInt.shift_right_big_int x y)
in (int_as_bounded1 r int_to_t1 uu____10434))
end)))), (uu____10324))))
in (uu____10294)::[])
in (uu____10118)::uu____10263))
in (uu____9994)::uu____10087))
in (uu____9822)::uu____9963))
in (uu____9650)::uu____9791))
in (uu____9478)::uu____9619)))))
in (FStar_List.append add_sub_mul_v (FStar_List.append div_mod_unsigned bitwise)))))))))
in (

let strong_steps = (FStar_List.map (as_primitive_step true) (FStar_List.append basic_ops bounded_arith_ops))
in (

let weak_steps = (FStar_List.map (as_primitive_step false) weak_ops)
in (FStar_All.pipe_left prim_from_list (FStar_List.append strong_steps weak_steps))))))))))))))))))))))))))))))))))))


let equality_ops : primitive_step FStar_Util.psmap = (

let interp_prop_eq21 = (fun psc _norm_cb args -> (

let r = psc.psc_range
in (match (args) with
| ((_typ, uu____10813))::((a1, uu____10815))::((a2, uu____10817))::[] -> begin
(

let uu____10874 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____10874) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___267_10878 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___267_10878.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___267_10878.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___268_10880 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___268_10880.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___268_10880.FStar_Syntax_Syntax.vars}))
end
| uu____10881 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____10882 -> begin
(failwith "Unexpected number of arguments")
end)))
in (

let interp_prop_eq31 = (fun psc _norm_cb args -> (

let r = psc.psc_range
in (match (args) with
| ((t1, uu____10913))::((t2, uu____10915))::((a1, uu____10917))::((a2, uu____10919))::[] -> begin
(

let uu____10992 = (

let uu____10993 = (FStar_Syntax_Util.eq_tm t1 t2)
in (

let uu____10994 = (FStar_Syntax_Util.eq_tm a1 a2)
in (FStar_Syntax_Util.eq_inj uu____10993 uu____10994)))
in (match (uu____10992) with
| FStar_Syntax_Util.Equal -> begin
FStar_Pervasives_Native.Some ((

let uu___269_10998 = FStar_Syntax_Util.t_true
in {FStar_Syntax_Syntax.n = uu___269_10998.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___269_10998.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Pervasives_Native.Some ((

let uu___270_11000 = FStar_Syntax_Util.t_false
in {FStar_Syntax_Syntax.n = uu___270_11000.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___270_11000.FStar_Syntax_Syntax.vars}))
end
| uu____11001 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____11002 -> begin
(failwith "Unexpected number of arguments")
end)))
in (

let propositional_equality = {name = FStar_Parser_Const.eq2_lid; arity = (Prims.parse_int "3"); univ_arity = (Prims.parse_int "1"); auto_reflect = FStar_Pervasives_Native.None; strong_reduction_ok = true; requires_binder_substitution = false; interpretation = interp_prop_eq21; interpretation_nbe = (fun _cb -> FStar_TypeChecker_NBETerm.interp_prop_eq2)}
in (

let hetero_propositional_equality = {name = FStar_Parser_Const.eq3_lid; arity = (Prims.parse_int "4"); univ_arity = (Prims.parse_int "2"); auto_reflect = FStar_Pervasives_Native.None; strong_reduction_ok = true; requires_binder_substitution = false; interpretation = interp_prop_eq31; interpretation_nbe = (fun _cb -> FStar_TypeChecker_NBETerm.interp_prop_eq3)}
in (prim_from_list ((propositional_equality)::(hetero_propositional_equality)::[]))))))


let primop_time_map : Prims.int FStar_Util.smap = (FStar_Util.smap_create (Prims.parse_int "50"))


let primop_time_reset : unit  ->  unit = (fun uu____11017 -> (FStar_Util.smap_clear primop_time_map))


let primop_time_count : Prims.string  ->  Prims.int  ->  unit = (fun nm ms -> (

let uu____11028 = (FStar_Util.smap_try_find primop_time_map nm)
in (match (uu____11028) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.smap_add primop_time_map nm ms)
end
| FStar_Pervasives_Native.Some (ms0) -> begin
(FStar_Util.smap_add primop_time_map nm (ms0 + ms))
end)))


let fixto : Prims.int  ->  Prims.string  ->  Prims.string = (fun n1 s -> (match (((FStar_String.length s) < n1)) with
| true -> begin
(

let uu____11042 = (FStar_String.make (n1 - (FStar_String.length s)) 32 (* *))
in (Prims.strcat uu____11042 s))
end
| uu____11044 -> begin
s
end))


let primop_time_report : unit  ->  Prims.string = (fun uu____11049 -> (

let pairs = (FStar_Util.smap_fold primop_time_map (fun nm ms rest -> (((nm), (ms)))::rest) [])
in (

let pairs1 = (FStar_Util.sort_with (fun uu____11100 uu____11101 -> (match (((uu____11100), (uu____11101))) with
| ((uu____11118, t1), (uu____11120, t2)) -> begin
(t1 - t2)
end)) pairs)
in (FStar_List.fold_right (fun uu____11139 rest -> (match (uu____11139) with
| (nm, ms) -> begin
(

let uu____11147 = (

let uu____11148 = (

let uu____11149 = (FStar_Util.string_of_int ms)
in (fixto (Prims.parse_int "10") uu____11149))
in (FStar_Util.format2 "%sms --- %s\n" uu____11148 nm))
in (Prims.strcat uu____11147 rest))
end)) pairs1 ""))))


let plugins : ((primitive_step  ->  unit) * (unit  ->  primitive_step Prims.list)) = (

let plugins = (FStar_Util.mk_ref [])
in (

let register = (fun p -> (

let uu____11175 = (

let uu____11178 = (FStar_ST.op_Bang plugins)
in (p)::uu____11178)
in (FStar_ST.op_Colon_Equals plugins uu____11175)))
in (

let retrieve = (fun uu____11278 -> (FStar_ST.op_Bang plugins))
in ((register), (retrieve)))))


let register_plugin : primitive_step  ->  unit = (fun p -> (FStar_Pervasives_Native.fst plugins p))


let retrieve_plugins : unit  ->  primitive_step Prims.list = (fun uu____11351 -> (

let uu____11352 = (FStar_Options.no_plugins ())
in (match (uu____11352) with
| true -> begin
[]
end
| uu____11355 -> begin
(FStar_Pervasives_Native.snd plugins ())
end)))


let config' : primitive_step Prims.list  ->  FStar_TypeChecker_Env.step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun psteps s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun uu___237_11396 -> (match (uu___237_11396) with
| FStar_TypeChecker_Env.UnfoldUntil (k) -> begin
(FStar_TypeChecker_Env.Unfold (k))::[]
end
| FStar_TypeChecker_Env.Eager_unfolding -> begin
(FStar_TypeChecker_Env.Eager_unfolding_only)::[]
end
| FStar_TypeChecker_Env.Inlining -> begin
(FStar_TypeChecker_Env.InliningDelta)::[]
end
| uu____11400 -> begin
[]
end))))
in (

let d1 = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| uu____11406 -> begin
d
end)
in (

let uu____11409 = (to_fsteps s)
in (

let uu____11410 = (

let uu____11411 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("Norm")))
in (

let uu____11412 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("NormTop")))
in (

let uu____11413 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("NormCfg")))
in (

let uu____11414 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("Primops")))
in (

let uu____11415 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("Unfolding")))
in (

let uu____11416 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("380")))
in (

let uu____11417 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("WPE")))
in (

let uu____11418 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("NormDelayed")))
in (

let uu____11419 = (FStar_TypeChecker_Env.debug e (FStar_Options.Other ("print_normalized_terms")))
in {gen = uu____11411; top = uu____11412; cfg = uu____11413; primop = uu____11414; unfolding = uu____11415; b380 = uu____11416; wpe = uu____11417; norm_delayed = uu____11418; print_normalized = uu____11419})))))))))
in (

let uu____11420 = (

let uu____11423 = (

let uu____11426 = (retrieve_plugins ())
in (FStar_List.append uu____11426 psteps))
in (add_steps built_in_primitive_steps uu____11423))
in (

let uu____11429 = ((FStar_Options.normalize_pure_terms_for_extraction ()) || (

let uu____11431 = (FStar_All.pipe_right s (FStar_Util.for_some (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.PureSubtermsWithinComputations)))
in (not (uu____11431))))
in {steps = uu____11409; tcenv = e; debug = uu____11410; delta_level = d1; primitive_steps = uu____11420; strong = false; memoize_lazy = true; normalize_pure_lets = uu____11429; reifying = false})))))))


let config : FStar_TypeChecker_Env.step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (config' [] s e))




