
let handle_err = (fun ( warning ) ( ret ) ( e ) -> (match (e) with
| Microsoft_FStar_Absyn_Syntax.Error ((msg, r)) -> begin
(let _23_34 = (let _68_8423 = (let _68_8422 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format3 "%s : %s\n%s\n" _68_8422 (match (warning) with
| true -> begin
"Warning"
end
| false -> begin
"Error"
end) msg))
in (Support.Microsoft.FStar.Util.print_string _68_8423))
in ())
end
| Support.Microsoft.FStar.Util.NYI (s) -> begin
(let _23_38 = (let _68_8424 = (Support.Microsoft.FStar.Util.format1 "Feature not yet implemented: %s" s)
in (Support.Microsoft.FStar.Util.print_string _68_8424))
in ())
end
| Microsoft_FStar_Absyn_Syntax.Err (s) -> begin
(let _68_8425 = (Support.Microsoft.FStar.Util.format1 "Error: %s" s)
in (Support.Microsoft.FStar.Util.print_string _68_8425))
end
| _23_43 -> begin
(raise (e))
end))

let handleable = (fun ( _23_1 ) -> (match (_23_1) with
| (Microsoft_FStar_Absyn_Syntax.Error (_)) | (Support.Microsoft.FStar.Util.NYI (_)) | (Microsoft_FStar_Absyn_Syntax.Err (_)) -> begin
true
end
| _23_55 -> begin
false
end))

type gensym_t =
{gensym : unit  ->  string; reset : unit  ->  unit}

let is_Mkgensym_t = (fun ( _ ) -> (failwith ("Not yet implemented:is_Mkgensym_t")))

let gs = (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (let n_resets = (Support.Microsoft.FStar.Util.mk_ref 0)
in {gensym = (fun ( _23_61 ) -> (match (()) with
| () -> begin
(let _68_8453 = (let _68_8450 = (let _68_8449 = (let _68_8448 = (Support.ST.read n_resets)
in (Support.Microsoft.FStar.Util.string_of_int _68_8448))
in (Support.String.strcat "_" _68_8449))
in (Support.String.strcat _68_8450 "_"))
in (let _68_8452 = (let _68_8451 = (let _23_62 = (Support.Microsoft.FStar.Util.incr ctr)
in (Support.ST.read ctr))
in (Support.Microsoft.FStar.Util.string_of_int _68_8451))
in (Support.String.strcat _68_8453 _68_8452)))
end)); reset = (fun ( _23_64 ) -> (match (()) with
| () -> begin
(let _23_65 = (Support.ST.op_Colon_Equals ctr 0)
in (Support.Microsoft.FStar.Util.incr n_resets))
end))}))

let gensym = (fun ( _23_67 ) -> (match (()) with
| () -> begin
(gs.gensym ())
end))

let reset_gensym = (fun ( _23_68 ) -> (match (()) with
| () -> begin
(gs.reset ())
end))

let rec gensyms = (fun ( x ) -> (match (x) with
| 0 -> begin
[]
end
| n -> begin
(let _68_8462 = (gensym ())
in (let _68_8461 = (gensyms (n - 1))
in (_68_8462)::_68_8461))
end))

let genident = (fun ( r ) -> (let sym = (gensym ())
in (match (r) with
| None -> begin
(Microsoft_FStar_Absyn_Syntax.mk_ident (sym, Microsoft_FStar_Absyn_Syntax.dummyRange))
end
| Some (r) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_ident (sym, r))
end)))

let bvd_eq = (fun ( bvd1 ) ( bvd2 ) -> (bvd1.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText = bvd2.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText))

let range_of_bvd = (fun ( x ) -> x.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idRange)

let mkbvd = (fun ( _23_82 ) -> (match (_23_82) with
| (x, y) -> begin
{Microsoft_FStar_Absyn_Syntax.ppname = x; Microsoft_FStar_Absyn_Syntax.realname = y}
end))

let setsort = (fun ( w ) ( t ) -> {Microsoft_FStar_Absyn_Syntax.v = w.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = w.Microsoft_FStar_Absyn_Syntax.p})

let withinfo = (fun ( e ) ( s ) ( r ) -> {Microsoft_FStar_Absyn_Syntax.v = e; Microsoft_FStar_Absyn_Syntax.sort = s; Microsoft_FStar_Absyn_Syntax.p = r})

let withsort = (fun ( e ) ( s ) -> (withinfo e s Microsoft_FStar_Absyn_Syntax.dummyRange))

let bvar_ppname = (fun ( bv ) -> bv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname)

let bvar_realname = (fun ( bv ) -> bv.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.realname)

let bvar_eq = (fun ( bv1 ) ( bv2 ) -> (bvd_eq bv1.Microsoft_FStar_Absyn_Syntax.v bv2.Microsoft_FStar_Absyn_Syntax.v))

let lbname_eq = (fun ( l1 ) ( l2 ) -> (match ((l1, l2)) with
| (Support.Microsoft.FStar.Util.Inl (x), Support.Microsoft.FStar.Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (Support.Microsoft.FStar.Util.Inr (l), Support.Microsoft.FStar.Util.Inr (m)) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l m)
end
| _23_109 -> begin
false
end))

let fvar_eq = (fun ( fv1 ) ( fv2 ) -> (Microsoft_FStar_Absyn_Syntax.lid_equals fv1.Microsoft_FStar_Absyn_Syntax.v fv2.Microsoft_FStar_Absyn_Syntax.v))

let bvd_to_bvar_s = (fun ( bvd ) ( sort ) -> {Microsoft_FStar_Absyn_Syntax.v = bvd; Microsoft_FStar_Absyn_Syntax.sort = sort; Microsoft_FStar_Absyn_Syntax.p = bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idRange})

let bvar_to_bvd = (fun ( bv ) -> bv.Microsoft_FStar_Absyn_Syntax.v)

let btvar_to_typ = (fun ( bv ) -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_btvar bv None bv.Microsoft_FStar_Absyn_Syntax.p))

let bvd_to_typ = (fun ( bvd ) ( k ) -> (btvar_to_typ (bvd_to_bvar_s bvd k)))

let bvar_to_exp = (fun ( bv ) -> (Microsoft_FStar_Absyn_Syntax.mk_Exp_bvar bv None bv.Microsoft_FStar_Absyn_Syntax.p))

let bvd_to_exp = (fun ( bvd ) ( t ) -> (bvar_to_exp (bvd_to_bvar_s bvd t)))

let new_bvd = (fun ( ropt ) -> (let f = (fun ( ropt ) -> (let id = (genident ropt)
in (mkbvd (id, id))))
in (f ropt)))

let freshen_bvd = (fun ( bvd' ) -> (let _68_8503 = (let _68_8502 = (genident (Some ((range_of_bvd bvd'))))
in (bvd'.Microsoft_FStar_Absyn_Syntax.ppname, _68_8502))
in (mkbvd _68_8503)))

let freshen_bvar = (fun ( b ) -> (let _68_8505 = (freshen_bvd b.Microsoft_FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _68_8505 b.Microsoft_FStar_Absyn_Syntax.sort)))

let gen_bvar = (fun ( sort ) -> (let bvd = (new_bvd None)
in (bvd_to_bvar_s bvd sort)))

let gen_bvar_p = (fun ( r ) ( sort ) -> (let bvd = (new_bvd (Some (r)))
in (bvd_to_bvar_s bvd sort)))

let bvdef_of_str = (fun ( s ) -> (let f = (fun ( s ) -> (let id = (Microsoft_FStar_Absyn_Syntax.id_of_text s)
in (mkbvd (id, id))))
in (f s)))

let set_bvd_range = (fun ( bvd ) ( r ) -> (let _68_8514 = (Microsoft_FStar_Absyn_Syntax.mk_ident (bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText, r))
in (let _68_8513 = (Microsoft_FStar_Absyn_Syntax.mk_ident (bvd.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText, r))
in {Microsoft_FStar_Absyn_Syntax.ppname = _68_8514; Microsoft_FStar_Absyn_Syntax.realname = _68_8513})))

let set_lid_range = (fun ( l ) ( r ) -> (let ids = (Support.Prims.pipe_right (Support.List.append l.Microsoft_FStar_Absyn_Syntax.ns ((l.Microsoft_FStar_Absyn_Syntax.ident)::[])) (Support.List.map (fun ( i ) -> (Microsoft_FStar_Absyn_Syntax.mk_ident (i.Microsoft_FStar_Absyn_Syntax.idText, r)))))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids ids)))

let fv = (fun ( l ) -> (let _68_8522 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l Microsoft_FStar_Absyn_Syntax.tun _68_8522)))

let fvvar_of_lid = (fun ( l ) ( t ) -> (let _68_8525 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l t _68_8525)))

let fvar = (fun ( dc ) ( l ) ( r ) -> (let _68_8534 = (let _68_8533 = (let _68_8532 = (set_lid_range l r)
in (fv _68_8532))
in (_68_8533, dc))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar _68_8534 None r)))

let ftv = (fun ( l ) ( k ) -> (let _68_8541 = (let _68_8539 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (withinfo l k _68_8539))
in (let _68_8540 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_const _68_8541 None _68_8540))))

let order_bvd = (fun ( x ) ( y ) -> (match ((x, y)) with
| (Support.Microsoft.FStar.Util.Inl (_23_155), Support.Microsoft.FStar.Util.Inr (_23_158)) -> begin
(- (1))
end
| (Support.Microsoft.FStar.Util.Inr (_23_162), Support.Microsoft.FStar.Util.Inl (_23_165)) -> begin
1
end
| (Support.Microsoft.FStar.Util.Inl (x), Support.Microsoft.FStar.Util.Inl (y)) -> begin
(Support.String.compare x.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText y.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Support.String.compare x.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText y.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText)
end))

let arg_of_non_null_binder = (fun ( _23_180 ) -> (match (_23_180) with
| (b, imp) -> begin
(match (b) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _68_8546 = (let _68_8545 = (btvar_to_typ a)
in Support.Microsoft.FStar.Util.Inl (_68_8545))
in (_68_8546, imp))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _68_8548 = (let _68_8547 = (bvar_to_exp x)
in Support.Microsoft.FStar.Util.Inr (_68_8547))
in (_68_8548, imp))
end)
end))

let args_of_non_null_binders = (fun ( binders ) -> (Support.Prims.pipe_right binders (Support.List.collect (fun ( b ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
[]
end
| false -> begin
(let _68_8552 = (arg_of_non_null_binder b)
in (_68_8552)::[])
end)))))

let args_of_binders = (fun ( binders ) -> (let _68_8562 = (Support.Prims.pipe_right binders (Support.List.map (fun ( b ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
(let b = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _68_8557 = (let _68_8556 = (gen_bvar a.Microsoft_FStar_Absyn_Syntax.sort)
in Support.Microsoft.FStar.Util.Inl (_68_8556))
in (_68_8557, (Support.Prims.snd b)))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _68_8559 = (let _68_8558 = (gen_bvar x.Microsoft_FStar_Absyn_Syntax.sort)
in Support.Microsoft.FStar.Util.Inr (_68_8558))
in (_68_8559, (Support.Prims.snd b)))
end)
in (let _68_8560 = (arg_of_non_null_binder b)
in (b, _68_8560)))
end
| false -> begin
(let _68_8561 = (arg_of_non_null_binder b)
in (b, _68_8561))
end))))
in (Support.Prims.pipe_right _68_8562 Support.List.unzip)))

let name_binders = (fun ( binders ) -> (Support.Prims.pipe_right binders (Support.List.mapi (fun ( i ) ( b ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
(match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let b = (let _68_8568 = (let _68_8567 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.String.strcat "_" _68_8567))
in (Microsoft_FStar_Absyn_Syntax.id_of_text _68_8568))
in (let b = (bvd_to_bvar_s (mkbvd (b, b)) a.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.Inl (b), imp)))
end
| (Support.Microsoft.FStar.Util.Inr (y), imp) -> begin
(let x = (let _68_8570 = (let _68_8569 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.String.strcat "_" _68_8569))
in (Microsoft_FStar_Absyn_Syntax.id_of_text _68_8570))
in (let x = (bvd_to_bvar_s (mkbvd (x, x)) y.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.Microsoft.FStar.Util.Inr (x), imp)))
end)
end
| false -> begin
b
end)))))

let name_function_binders = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, comp)) -> begin
(let _68_8574 = (let _68_8573 = (name_binders binders)
in (_68_8573, comp))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _68_8574 None t.Microsoft_FStar_Absyn_Syntax.pos))
end
| _23_215 -> begin
t
end))

let null_binders_of_tks = (fun ( tks ) -> (Support.Prims.pipe_right tks (Support.List.map (fun ( _23_2 ) -> (match (_23_2) with
| (Support.Microsoft.FStar.Util.Inl (k), imp) -> begin
(let _68_8579 = (let _68_8578 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (Support.Prims.pipe_left Support.Prims.fst _68_8578))
in (_68_8579, imp))
end
| (Support.Microsoft.FStar.Util.Inr (t), imp) -> begin
(let _68_8581 = (let _68_8580 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (Support.Prims.pipe_left Support.Prims.fst _68_8580))
in (_68_8581, imp))
end)))))

let binders_of_tks = (fun ( tks ) -> (Support.Prims.pipe_right tks (Support.List.map (fun ( _23_3 ) -> (match (_23_3) with
| (Support.Microsoft.FStar.Util.Inl (k), imp) -> begin
(let _68_8586 = (let _68_8585 = (gen_bvar_p k.Microsoft_FStar_Absyn_Syntax.pos k)
in Support.Microsoft.FStar.Util.Inl (_68_8585))
in (_68_8586, imp))
end
| (Support.Microsoft.FStar.Util.Inr (t), imp) -> begin
(let _68_8588 = (let _68_8587 = (gen_bvar_p t.Microsoft_FStar_Absyn_Syntax.pos t)
in Support.Microsoft.FStar.Util.Inr (_68_8587))
in (_68_8588, imp))
end)))))

let binders_of_freevars = (fun ( fvs ) -> (let _68_8594 = (let _68_8591 = (Support.Microsoft.FStar.Util.set_elements fvs.Microsoft_FStar_Absyn_Syntax.ftvs)
in (Support.Prims.pipe_right _68_8591 (Support.List.map Microsoft_FStar_Absyn_Syntax.t_binder)))
in (let _68_8593 = (let _68_8592 = (Support.Microsoft.FStar.Util.set_elements fvs.Microsoft_FStar_Absyn_Syntax.fxvs)
in (Support.Prims.pipe_right _68_8592 (Support.List.map Microsoft_FStar_Absyn_Syntax.v_binder)))
in (Support.List.append _68_8594 _68_8593))))

let subst_to_string = (fun ( s ) -> (let _68_8597 = (Support.Prims.pipe_right s (Support.List.map (fun ( _23_4 ) -> (match (_23_4) with
| Support.Microsoft.FStar.Util.Inl ((b, _23_241)) -> begin
b.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText
end
| Support.Microsoft.FStar.Util.Inr ((x, _23_246)) -> begin
x.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText
end))))
in (Support.Prims.pipe_right _68_8597 (Support.String.concat ", "))))

let subst_tvar = (fun ( s ) ( a ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _23_5 ) -> (match (_23_5) with
| Support.Microsoft.FStar.Util.Inl ((b, t)) when (bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _23_257 -> begin
None
end))))

let subst_xvar = (fun ( s ) ( a ) -> (Support.Microsoft.FStar.Util.find_map s (fun ( _23_6 ) -> (match (_23_6) with
| Support.Microsoft.FStar.Util.Inr ((b, t)) when (bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _23_266 -> begin
None
end))))

let rec subst_typ' = (fun ( s ) ( t ) -> (match (s) with
| ([]) | ([]::[]) -> begin
(Microsoft_FStar_Absyn_Visit.compress_typ t)
end
| _23_273 -> begin
(let t0 = (Microsoft_FStar_Absyn_Visit.compress_typ t)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((Support.Microsoft.FStar.Util.Inl ((t', s')), m)) -> begin
(let _68_8622 = (let _68_8621 = (compose_subst s' s)
in (let _68_8620 = (Support.Microsoft.FStar.Util.mk_ref None)
in (t', _68_8621, _68_8620)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_delayed _68_8622 None t.Microsoft_FStar_Absyn_Syntax.pos))
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((Support.Microsoft.FStar.Util.Inr (mk_t), m)) -> begin
(let t = (mk_t ())
in (let _23_288 = (Support.ST.op_Colon_Equals m (Some (t)))
in (subst_typ' s t)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let rec aux = (fun ( s' ) -> (match (s') with
| s0::rest -> begin
(match ((subst_tvar s0 a)) with
| Some (t) -> begin
(subst_typ' rest t)
end
| _23_300 -> begin
(aux rest)
end)
end
| _23_302 -> begin
t0
end))
in (aux s))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
t0
end
| _23_311 -> begin
(let _68_8627 = (let _68_8626 = (Support.Microsoft.FStar.Util.mk_ref None)
in (t0, s, _68_8626))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_delayed _68_8627 None t.Microsoft_FStar_Absyn_Syntax.pos))
end))
end))
and subst_exp' = (fun ( s ) ( e ) -> (match (s) with
| ([]) | ([]::[]) -> begin
(Microsoft_FStar_Absyn_Visit.compress_exp e)
end
| _23_318 -> begin
(let e0 = (Microsoft_FStar_Absyn_Visit.compress_exp e)
in (match (e0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed ((e, s', m)) -> begin
(let _68_8632 = (let _68_8631 = (compose_subst s' s)
in (let _68_8630 = (Support.Microsoft.FStar.Util.mk_ref None)
in (e, _68_8631, _68_8630)))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_delayed _68_8632 None e.Microsoft_FStar_Absyn_Syntax.pos))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let rec aux = (fun ( s ) -> (match (s) with
| s0::rest -> begin
(match ((subst_xvar s0 x)) with
| Some (e) -> begin
(subst_exp' rest e)
end
| _23_335 -> begin
(aux rest)
end)
end
| _23_337 -> begin
e0
end))
in (aux s))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
e0
end
| _23_345 -> begin
(let _68_8636 = (let _68_8635 = (Support.Microsoft.FStar.Util.mk_ref None)
in (e0, s, _68_8635))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_delayed _68_8636 None e0.Microsoft_FStar_Absyn_Syntax.pos))
end))
end))
and subst_kind' = (fun ( s ) ( k ) -> (match (s) with
| ([]) | ([]::[]) -> begin
(Microsoft_FStar_Absyn_Visit.compress_kind k)
end
| _23_352 -> begin
(let k0 = (Microsoft_FStar_Absyn_Visit.compress_kind k)
in (match (k0.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) | (Microsoft_FStar_Absyn_Syntax.Kind_unknown) -> begin
k0
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed ((k, s', m)) -> begin
(let _68_8641 = (let _68_8640 = (compose_subst s' s)
in (let _68_8639 = (Support.Microsoft.FStar.Util.mk_ref None)
in (k, _68_8640, _68_8639)))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_delayed _68_8641 k0.Microsoft_FStar_Absyn_Syntax.pos))
end
| _23_363 -> begin
(let _68_8643 = (let _68_8642 = (Support.Microsoft.FStar.Util.mk_ref None)
in (k0, s, _68_8642))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_delayed _68_8643 k0.Microsoft_FStar_Absyn_Syntax.pos))
end))
end))
and subst_flags' = (fun ( s ) ( flags ) -> (Support.Prims.pipe_right flags (Support.List.map (fun ( _23_7 ) -> (match (_23_7) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (a) -> begin
(let _68_8647 = (subst_exp' s a)
in Microsoft_FStar_Absyn_Syntax.DECREASES (_68_8647))
end
| f -> begin
f
end)))))
and subst_comp_typ' = (fun ( s ) ( t ) -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _23_376 -> begin
(let _23_377 = t
in (let _68_8657 = (subst_typ' s t.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _68_8656 = (Support.List.map (fun ( _23_8 ) -> (match (_23_8) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _68_8652 = (let _68_8651 = (subst_typ' s t)
in Support.Microsoft.FStar.Util.Inl (_68_8651))
in (_68_8652, imp))
end
| (Support.Microsoft.FStar.Util.Inr (e), imp) -> begin
(let _68_8654 = (let _68_8653 = (subst_exp' s e)
in Support.Microsoft.FStar.Util.Inr (_68_8653))
in (_68_8654, imp))
end)) t.Microsoft_FStar_Absyn_Syntax.effect_args)
in (let _68_8655 = (subst_flags' s t.Microsoft_FStar_Absyn_Syntax.flags)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _23_377.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _68_8657; Microsoft_FStar_Absyn_Syntax.effect_args = _68_8656; Microsoft_FStar_Absyn_Syntax.flags = _68_8655}))))
end))
and subst_comp' = (fun ( s ) ( t ) -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _23_394 -> begin
(match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _68_8660 = (subst_typ' s t)
in (Microsoft_FStar_Absyn_Syntax.mk_Total _68_8660))
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _68_8661 = (subst_comp_typ' s ct)
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _68_8661))
end)
end))
and compose_subst = (fun ( s1 ) ( s2 ) -> (Support.List.append s1 s2))

let mk_subst = (fun ( s ) -> (s)::[])

let subst_kind = (fun ( s ) ( t ) -> (subst_kind' (mk_subst s) t))

let subst_typ = (fun ( s ) ( t ) -> (subst_typ' (mk_subst s) t))

let subst_exp = (fun ( s ) ( t ) -> (subst_exp' (mk_subst s) t))

let subst_flags = (fun ( s ) ( t ) -> (subst_flags' (mk_subst s) t))

let subst_comp = (fun ( s ) ( t ) -> (subst_comp' (mk_subst s) t))

let subst_binder = (fun ( s ) ( _23_9 ) -> (match (_23_9) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _68_8689 = (let _68_8688 = (let _23_418 = a
in (let _68_8687 = (subst_kind s a.Microsoft_FStar_Absyn_Syntax.sort)
in {Microsoft_FStar_Absyn_Syntax.v = _23_418.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _68_8687; Microsoft_FStar_Absyn_Syntax.p = _23_418.Microsoft_FStar_Absyn_Syntax.p}))
in Support.Microsoft.FStar.Util.Inl (_68_8688))
in (_68_8689, imp))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _68_8692 = (let _68_8691 = (let _23_424 = x
in (let _68_8690 = (subst_typ s x.Microsoft_FStar_Absyn_Syntax.sort)
in {Microsoft_FStar_Absyn_Syntax.v = _23_424.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = _68_8690; Microsoft_FStar_Absyn_Syntax.p = _23_424.Microsoft_FStar_Absyn_Syntax.p}))
in Support.Microsoft.FStar.Util.Inr (_68_8691))
in (_68_8692, imp))
end))

let subst_arg = (fun ( s ) ( _23_10 ) -> (match (_23_10) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _68_8696 = (let _68_8695 = (subst_typ s t)
in Support.Microsoft.FStar.Util.Inl (_68_8695))
in (_68_8696, imp))
end
| (Support.Microsoft.FStar.Util.Inr (e), imp) -> begin
(let _68_8698 = (let _68_8697 = (subst_exp s e)
in Support.Microsoft.FStar.Util.Inr (_68_8697))
in (_68_8698, imp))
end))

let subst_binders = (fun ( s ) ( bs ) -> (match (s) with
| [] -> begin
bs
end
| _23_440 -> begin
(Support.List.map (subst_binder s) bs)
end))

let subst_args = (fun ( s ) ( args ) -> (match (s) with
| [] -> begin
args
end
| _23_445 -> begin
(Support.List.map (subst_arg s) args)
end))

let subst_formal = (fun ( f ) ( a ) -> (match ((f, a)) with
| ((Support.Microsoft.FStar.Util.Inl (a), _23_451), (Support.Microsoft.FStar.Util.Inl (t), _23_456)) -> begin
Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, t))
end
| ((Support.Microsoft.FStar.Util.Inr (x), _23_462), (Support.Microsoft.FStar.Util.Inr (v), _23_467)) -> begin
Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, v))
end
| _23_471 -> begin
(failwith ("Ill-formed substitution"))
end))

let mk_subst_one_binder = (fun ( b1 ) ( b2 ) -> (match (((Microsoft_FStar_Absyn_Syntax.is_null_binder b1) || (Microsoft_FStar_Absyn_Syntax.is_null_binder b2))) with
| true -> begin
[]
end
| false -> begin
(match (((Support.Prims.fst b1), (Support.Prims.fst b2))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(match ((bvar_eq a b)) with
| true -> begin
[]
end
| false -> begin
(let _68_8713 = (let _68_8712 = (let _68_8711 = (btvar_to_typ a)
in (b.Microsoft_FStar_Absyn_Syntax.v, _68_8711))
in Support.Microsoft.FStar.Util.Inl (_68_8712))
in (_68_8713)::[])
end)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(match ((bvar_eq x y)) with
| true -> begin
[]
end
| false -> begin
(let _68_8716 = (let _68_8715 = (let _68_8714 = (bvar_to_exp x)
in (y.Microsoft_FStar_Absyn_Syntax.v, _68_8714))
in Support.Microsoft.FStar.Util.Inr (_68_8715))
in (_68_8716)::[])
end)
end
| _23_485 -> begin
[]
end)
end))

let mk_subst_binder = (fun ( bs1 ) ( bs2 ) -> (let rec aux = (fun ( out ) ( bs1 ) ( bs2 ) -> (match ((bs1, bs2)) with
| ([], []) -> begin
Some (out)
end
| (b1::bs1, b2::bs2) -> begin
(let _68_8728 = (let _68_8727 = (mk_subst_one_binder b1 b2)
in (Support.List.append _68_8727 out))
in (aux _68_8728 bs1 bs2))
end
| _23_503 -> begin
None
end))
in (aux [] bs1 bs2)))

let subst_of_list = (fun ( formals ) ( actuals ) -> (match (((Support.List.length formals) = (Support.List.length actuals))) with
| true -> begin
(Support.List.map2 subst_formal formals actuals)
end
| false -> begin
(failwith ("Ill-formed substitution"))
end))

type red_ctrl =
{stop_if_empty_subst : bool; descend : bool}

let is_Mkred_ctrl = (fun ( _ ) -> (failwith ("Not yet implemented:is_Mkred_ctrl")))

let alpha_ctrl = {stop_if_empty_subst = false; descend = true}

let subst_ctrl = {stop_if_empty_subst = true; descend = true}

let null_ctrl = {stop_if_empty_subst = true; descend = false}

let extend_subst = (fun ( e ) ( s ) -> (Support.List.append (((mk_subst e))::[]) s))

let map_knd = (fun ( s ) ( vk ) ( mt ) ( me ) ( descend ) ( binders ) ( k ) -> (let _68_8749 = (subst_kind' s k)
in (_68_8749, descend)))

let map_typ = (fun ( s ) ( mk ) ( vt ) ( me ) ( descend ) ( binders ) ( t ) -> (let _68_8757 = (subst_typ' s t)
in (_68_8757, descend)))

let map_exp = (fun ( s ) ( mk ) ( me ) ( ve ) ( descend ) ( binders ) ( e ) -> (let _68_8765 = (subst_exp' s e)
in (_68_8765, descend)))

let map_flags = (fun ( s ) ( map_exp ) ( descend ) ( binders ) ( flags ) -> (Support.Prims.pipe_right flags (Support.List.map (fun ( _23_11 ) -> (match (_23_11) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _68_8782 = (let _68_8781 = (map_exp descend binders e)
in (Support.Prims.pipe_right _68_8781 Support.Prims.fst))
in Microsoft_FStar_Absyn_Syntax.DECREASES (_68_8782))
end
| f -> begin
f
end)))))

let map_comp = (fun ( s ) ( mk ) ( map_typ ) ( map_exp ) ( descend ) ( binders ) ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _23_552 = (map_typ descend binders t)
in (match (_23_552) with
| (t, descend) -> begin
(let _68_8805 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (_68_8805, descend))
end))
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _23_557 = (map_typ descend binders ct.Microsoft_FStar_Absyn_Syntax.result_typ)
in (match (_23_557) with
| (t, descend) -> begin
(let _23_560 = (Microsoft_FStar_Absyn_Visit.map_args map_typ map_exp descend binders ct.Microsoft_FStar_Absyn_Syntax.effect_args)
in (match (_23_560) with
| (args, descend) -> begin
(let _68_8808 = (let _68_8807 = (let _23_561 = ct
in (let _68_8806 = (map_flags s map_exp descend binders ct.Microsoft_FStar_Absyn_Syntax.flags)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _23_561.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = args; Microsoft_FStar_Absyn_Syntax.flags = _68_8806}))
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _68_8807))
in (_68_8808, descend))
end))
end))
end))

let visit_knd = (fun ( s ) ( vk ) ( mt ) ( me ) ( ctrl ) ( binders ) ( k ) -> (let k = (Microsoft_FStar_Absyn_Visit.compress_kind k)
in (match (ctrl.descend) with
| true -> begin
(let _23_574 = (vk null_ctrl binders k)
in (match (_23_574) with
| (k, _23_573) -> begin
(k, ctrl)
end))
end
| false -> begin
(map_knd s vk mt me null_ctrl binders k)
end)))

let rec compress_kind = (fun ( k ) -> (let k = (Microsoft_FStar_Absyn_Visit.compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_delayed ((k', s, m)) -> begin
(let k' = (let _68_8854 = (Microsoft_FStar_Absyn_Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) Microsoft_FStar_Absyn_Visit.combine_kind Microsoft_FStar_Absyn_Visit.combine_typ Microsoft_FStar_Absyn_Visit.combine_exp subst_ctrl [] k')
in (Support.Prims.pipe_left Support.Prims.fst _68_8854))
in (let k' = (compress_kind k')
in (let _23_584 = (Support.ST.op_Colon_Equals m (Some (k')))
in k')))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, actuals)) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (k) -> begin
(match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam ((formals, k')) -> begin
(let _68_8856 = (let _68_8855 = (subst_of_list formals actuals)
in (subst_kind _68_8855 k'))
in (compress_kind _68_8856))
end
| _23_597 -> begin
(match (((Support.List.length actuals) = 0)) with
| true -> begin
k
end
| false -> begin
(failwith ("Wrong arity for kind unifier"))
end)
end)
end
| _23_599 -> begin
k
end)
end
| _23_601 -> begin
k
end)))

let rec visit_typ = (fun ( s ) ( mk ) ( vt ) ( me ) ( ctrl ) ( boundvars ) ( t ) -> (let visit_prod = (fun ( bs ) ( tc ) -> (let _23_662 = (Support.Prims.pipe_right bs (Support.List.fold_left (fun ( _23_615 ) ( b ) -> (match (_23_615) with
| (bs, boundvars, s) -> begin
(match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _23_624 = (map_knd s mk vt me null_ctrl boundvars a.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_23_624) with
| (k, _23_623) -> begin
(let a = (let _23_625 = a
in {Microsoft_FStar_Absyn_Syntax.v = _23_625.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _23_625.Microsoft_FStar_Absyn_Syntax.p})
in (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
(((Support.Microsoft.FStar.Util.Inl (a), imp))::bs, boundvars, s)
end
| false -> begin
(let boundvars' = (Support.Microsoft.FStar.Util.Inl (a.Microsoft_FStar_Absyn_Syntax.v))::boundvars
in (let _23_637 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(Support.Microsoft.FStar.Util.Inl (a), s, boundvars')
end
| _23_631 -> begin
(let b = (let _68_8933 = (freshen_bvd a.Microsoft_FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _68_8933 k))
in (let s = (let _68_8936 = (let _68_8935 = (let _68_8934 = (btvar_to_typ b)
in (a.Microsoft_FStar_Absyn_Syntax.v, _68_8934))
in Support.Microsoft.FStar.Util.Inl (_68_8935))
in (extend_subst _68_8936 s))
in (Support.Microsoft.FStar.Util.Inl (b), s, (Support.Microsoft.FStar.Util.Inl (b.Microsoft_FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_23_637) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end))
end))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _23_645 = (map_typ s mk vt me null_ctrl boundvars x.Microsoft_FStar_Absyn_Syntax.sort)
in (match (_23_645) with
| (t, _23_644) -> begin
(let x = (let _23_646 = x
in {Microsoft_FStar_Absyn_Syntax.v = _23_646.Microsoft_FStar_Absyn_Syntax.v; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _23_646.Microsoft_FStar_Absyn_Syntax.p})
in (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
(((Support.Microsoft.FStar.Util.Inr (x), imp))::bs, boundvars, s)
end
| false -> begin
(let boundvars' = (Support.Microsoft.FStar.Util.Inr (x.Microsoft_FStar_Absyn_Syntax.v))::boundvars
in (let _23_658 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(Support.Microsoft.FStar.Util.Inr (x), s, boundvars')
end
| _23_652 -> begin
(let y = (let _68_8946 = (freshen_bvd x.Microsoft_FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _68_8946 t))
in (let s = (let _68_8949 = (let _68_8948 = (let _68_8947 = (bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _68_8947))
in Support.Microsoft.FStar.Util.Inr (_68_8948))
in (extend_subst _68_8949 s))
in (Support.Microsoft.FStar.Util.Inr (y), s, (Support.Microsoft.FStar.Util.Inr (y.Microsoft_FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_23_658) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end))
end))
end)
end)) ([], boundvars, s)))
in (match (_23_662) with
| (bs, boundvars, s) -> begin
(let tc = (match ((s, tc)) with
| ([], _23_665) -> begin
tc
end
| (_23_668, Support.Microsoft.FStar.Util.Inl (t)) -> begin
(let _68_8960 = (let _68_8959 = (map_typ s mk vt me null_ctrl boundvars t)
in (Support.Prims.pipe_left Support.Prims.fst _68_8959))
in Support.Microsoft.FStar.Util.Inl (_68_8960))
end
| (_23_673, Support.Microsoft.FStar.Util.Inr (c)) -> begin
(let _68_8983 = (let _68_8982 = (map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl boundvars c)
in (Support.Prims.pipe_left Support.Prims.fst _68_8982))
in Support.Microsoft.FStar.Util.Inr (_68_8983))
end)
in ((Support.List.rev bs), tc))
end)))
in (let t0 = t
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (_23_680) -> begin
(let _68_8985 = (let _68_8984 = (subst_typ' s t0)
in (Support.Prims.pipe_left compress_typ _68_8984))
in (_68_8985, ctrl))
end
| _23_683 when (not (ctrl.descend)) -> begin
(map_typ s mk vt me null_ctrl boundvars t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(match ((visit_prod bs (Support.Microsoft.FStar.Util.Inr (c)))) with
| (bs, Support.Microsoft.FStar.Util.Inr (c)) -> begin
(let _68_8995 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t0.Microsoft_FStar_Absyn_Syntax.pos)
in (_68_8995, ctrl))
end
| _23_693 -> begin
(failwith ("Impossible"))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, t)) -> begin
(match ((visit_prod (((Support.Microsoft.FStar.Util.Inr (x), None))::[]) (Support.Microsoft.FStar.Util.Inl (t)))) with
| ((Support.Microsoft.FStar.Util.Inr (x), _23_701)::[], Support.Microsoft.FStar.Util.Inl (t)) -> begin
(let _68_8996 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_refine (x, t) None t0.Microsoft_FStar_Absyn_Syntax.pos)
in (_68_8996, ctrl))
end
| _23_708 -> begin
(failwith ("Impossible"))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(match ((visit_prod bs (Support.Microsoft.FStar.Util.Inl (t)))) with
| (bs, Support.Microsoft.FStar.Util.Inl (t)) -> begin
(let _68_8997 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t0.Microsoft_FStar_Absyn_Syntax.pos)
in (_68_8997, ctrl))
end
| _23_718 -> begin
(failwith ("Impossible"))
end)
end
| _23_720 -> begin
(let _23_724 = (vt null_ctrl boundvars t)
in (match (_23_724) with
| (t, _23_723) -> begin
(t, ctrl)
end))
end))))
and compress_typ' = (fun ( t ) -> (let t = (Microsoft_FStar_Absyn_Visit.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((Support.Microsoft.FStar.Util.Inl ((t', s)), m)) -> begin
(let res = (let _68_9017 = (Microsoft_FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) Microsoft_FStar_Absyn_Visit.combine_kind Microsoft_FStar_Absyn_Visit.combine_typ Microsoft_FStar_Absyn_Visit.combine_exp subst_ctrl [] t')
in (Support.Prims.pipe_left Support.Prims.fst _68_9017))
in (let res = (compress_typ' res)
in (let _23_736 = (Support.ST.op_Colon_Equals m (Some (res)))
in res)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed ((Support.Microsoft.FStar.Util.Inr (mk_t), m)) -> begin
(let t = (let _68_9019 = (mk_t ())
in (compress_typ' _68_9019))
in (let _23_744 = (Support.ST.op_Colon_Equals m (Some (t)))
in t))
end
| _23_747 -> begin
t
end)))
and compress_typ = (fun ( t ) -> (let t = (compress_typ' t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_23_751) -> begin
(failwith ("Impossible: compress returned a delayed type"))
end
| _23_754 -> begin
t
end)))

let rec visit_exp = (fun ( s ) ( mk ) ( me ) ( ve ) ( ctrl ) ( binders ) ( e ) -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (_23_764) -> begin
(let _68_9085 = (let _68_9084 = (subst_exp' s e)
in (Support.Prims.pipe_left compress_exp _68_9084))
in (_68_9085, ctrl))
end
| _23_767 when (not (ctrl.descend)) -> begin
(map_exp s mk me ve ctrl binders e)
end
| _23_769 -> begin
(let _23_773 = (ve null_ctrl binders e)
in (match (_23_773) with
| (e, _23_772) -> begin
(e, ctrl)
end))
end)))
and compress_exp = (fun ( e ) -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed ((e', s, m)) -> begin
(let e = (let _68_9114 = (Microsoft_FStar_Absyn_Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) Microsoft_FStar_Absyn_Visit.combine_kind Microsoft_FStar_Absyn_Visit.combine_typ Microsoft_FStar_Absyn_Visit.combine_exp subst_ctrl [] e')
in (Support.Prims.pipe_left Support.Prims.fst _68_9114))
in (let res = (compress_exp e)
in (let _23_783 = (Support.ST.op_Colon_Equals m (Some (res)))
in res)))
end
| _23_786 -> begin
e
end)))

let rec unmeta_exp = (fun ( e ) -> (let e = (compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _23_791))) -> begin
(unmeta_exp e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _23_797, _23_799)) -> begin
(unmeta_exp e)
end
| _23_803 -> begin
e
end)))

let alpha_typ = (fun ( t ) -> (let t = (compress_typ t)
in (let s = (mk_subst [])
in (let doit = (fun ( t ) -> (let _68_9139 = (Microsoft_FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) Microsoft_FStar_Absyn_Visit.combine_kind Microsoft_FStar_Absyn_Visit.combine_typ Microsoft_FStar_Absyn_Visit.combine_exp alpha_ctrl [] t)
in (Support.Prims.pipe_left Support.Prims.fst _68_9139)))
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, _))) -> begin
(match ((Support.Microsoft.FStar.Util.for_all Microsoft_FStar_Absyn_Syntax.is_null_binder bs)) with
| true -> begin
t
end
| false -> begin
(doit t)
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_23_819) -> begin
(doit t)
end
| _23_822 -> begin
t
end)))))

let formals_for_actuals = (fun ( formals ) ( actuals ) -> (Support.List.map2 (fun ( formal ) ( actual ) -> (match (((Support.Prims.fst formal), (Support.Prims.fst actual))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, b))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, y))
end
| _23_838 -> begin
(failwith ("Ill-typed substitution"))
end)) formals actuals))

let compress_typ_opt = (fun ( _23_12 ) -> (match (_23_12) with
| None -> begin
None
end
| Some (t) -> begin
(let _68_9146 = (compress_typ t)
in Some (_68_9146))
end))

let mk_discriminator = (fun ( lid ) -> (let _68_9151 = (let _68_9150 = (let _68_9149 = (Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.String.strcat "is_" lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText), lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idRange))
in (_68_9149)::[])
in (Support.List.append lid.Microsoft_FStar_Absyn_Syntax.ns _68_9150))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _68_9151)))

let is_name = (fun ( lid ) -> (let c = (Support.Microsoft.FStar.Util.char_at lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText 0)
in (Support.Microsoft.FStar.Util.is_upper c)))

let ml_comp = (fun ( t ) ( r ) -> (let _68_9159 = (let _68_9158 = (set_lid_range Microsoft_FStar_Absyn_Const.effect_ML_lid r)
in {Microsoft_FStar_Absyn_Syntax.effect_name = _68_9158; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = []; Microsoft_FStar_Absyn_Syntax.flags = (Microsoft_FStar_Absyn_Syntax.MLEFFECT)::[]})
in (Microsoft_FStar_Absyn_Syntax.mk_Comp _68_9159)))

let total_comp = (fun ( t ) ( r ) -> (Microsoft_FStar_Absyn_Syntax.mk_Total t))

let gtotal_comp = (fun ( t ) -> (Microsoft_FStar_Absyn_Syntax.mk_Comp {Microsoft_FStar_Absyn_Syntax.effect_name = Microsoft_FStar_Absyn_Const.effect_GTot_lid; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = []; Microsoft_FStar_Absyn_Syntax.flags = (Microsoft_FStar_Absyn_Syntax.SOMETRIVIAL)::[]}))

let comp_set_flags = (fun ( c ) ( f ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_23_854) -> begin
c
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(let _23_858 = c
in {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp ((let _23_860 = ct
in {Microsoft_FStar_Absyn_Syntax.effect_name = _23_860.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = _23_860.Microsoft_FStar_Absyn_Syntax.result_typ; Microsoft_FStar_Absyn_Syntax.effect_args = _23_860.Microsoft_FStar_Absyn_Syntax.effect_args; Microsoft_FStar_Absyn_Syntax.flags = f})); Microsoft_FStar_Absyn_Syntax.tk = _23_858.Microsoft_FStar_Absyn_Syntax.tk; Microsoft_FStar_Absyn_Syntax.pos = _23_858.Microsoft_FStar_Absyn_Syntax.pos; Microsoft_FStar_Absyn_Syntax.fvs = _23_858.Microsoft_FStar_Absyn_Syntax.fvs; Microsoft_FStar_Absyn_Syntax.uvs = _23_858.Microsoft_FStar_Absyn_Syntax.uvs})
end))

let comp_flags = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_23_864) -> begin
(Microsoft_FStar_Absyn_Syntax.TOTAL)::[]
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
ct.Microsoft_FStar_Absyn_Syntax.flags
end))

let comp_effect_name = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
c.Microsoft_FStar_Absyn_Syntax.effect_name
end
| Microsoft_FStar_Absyn_Syntax.Total (_23_872) -> begin
Microsoft_FStar_Absyn_Const.effect_Tot_lid
end))

let comp_to_comp_typ = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
c
end
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
{Microsoft_FStar_Absyn_Syntax.effect_name = Microsoft_FStar_Absyn_Const.effect_Tot_lid; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = []; Microsoft_FStar_Absyn_Syntax.flags = (Microsoft_FStar_Absyn_Syntax.TOTAL)::[]}
end))

let is_total_comp = (fun ( c ) -> (Support.Prims.pipe_right (comp_flags c) (Support.Microsoft.FStar.Util.for_some (fun ( _23_13 ) -> (match (_23_13) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _23_884 -> begin
false
end)))))

let is_total_lcomp = (fun ( c ) -> ((Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_Tot_lid) || (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.cflags (Support.Microsoft.FStar.Util.for_some (fun ( _23_14 ) -> (match (_23_14) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _23_890 -> begin
false
end))))))

let is_tot_or_gtot_lcomp = (fun ( c ) -> (((Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_Tot_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_GTot_lid)) || (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.cflags (Support.Microsoft.FStar.Util.for_some (fun ( _23_15 ) -> (match (_23_15) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _23_896 -> begin
false
end))))))

let is_partial_return = (fun ( c ) -> (Support.Prims.pipe_right (comp_flags c) (Support.Microsoft.FStar.Util.for_some (fun ( _23_16 ) -> (match (_23_16) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _23_902 -> begin
false
end)))))

let is_lcomp_partial_return = (fun ( c ) -> (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.cflags (Support.Microsoft.FStar.Util.for_some (fun ( _23_17 ) -> (match (_23_17) with
| (Microsoft_FStar_Absyn_Syntax.RETURN) | (Microsoft_FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _23_908 -> begin
false
end)))))

let is_tot_or_gtot_comp = (fun ( c ) -> ((is_total_comp c) || (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.effect_GTot_lid (comp_effect_name c))))

let is_pure_comp = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_23_912) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
((((is_tot_or_gtot_comp c) || (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_PURE_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Pure_lid)) || (Support.Prims.pipe_right ct.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _23_18 ) -> (match (_23_18) with
| Microsoft_FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _23_919 -> begin
false
end)))))
end))

let is_ghost_effect = (fun ( l ) -> (((Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.effect_GTot_lid l) || (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.effect_GHOST_lid l)) || (Microsoft_FStar_Absyn_Syntax.lid_equals Microsoft_FStar_Absyn_Const.effect_Ghost_lid l)))

let is_pure_or_ghost_comp = (fun ( c ) -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))

let is_pure_lcomp = (fun ( lc ) -> ((((is_total_lcomp lc) || (Microsoft_FStar_Absyn_Syntax.lid_equals lc.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_PURE_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals lc.Microsoft_FStar_Absyn_Syntax.eff_name Microsoft_FStar_Absyn_Const.effect_Pure_lid)) || (Support.Prims.pipe_right lc.Microsoft_FStar_Absyn_Syntax.cflags (Support.Microsoft.FStar.Util.for_some (fun ( _23_19 ) -> (match (_23_19) with
| Microsoft_FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _23_926 -> begin
false
end))))))

let is_pure_or_ghost_lcomp = (fun ( lc ) -> ((is_pure_lcomp lc) || (is_ghost_effect lc.Microsoft_FStar_Absyn_Syntax.eff_name)))

let is_pure_or_ghost_function = (fun ( t ) -> (match ((let _68_9198 = (compress_typ t)
in _68_9198.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((_23_930, c)) -> begin
(is_pure_or_ghost_comp c)
end
| _23_935 -> begin
true
end))

let is_lemma = (fun ( t ) -> (match ((let _68_9201 = (compress_typ t)
in _68_9201.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((_23_938, c)) -> begin
(match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Lemma_lid)
end
| _23_945 -> begin
false
end)
end
| _23_947 -> begin
false
end))

let is_smt_lemma = (fun ( t ) -> (match ((let _68_9204 = (compress_typ t)
in _68_9204.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((_23_950, c)) -> begin
(match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (ct) when (Microsoft_FStar_Absyn_Syntax.lid_equals ct.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_Lemma_lid) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| _req::_ens::(Support.Microsoft.FStar.Util.Inr (pats), _23_961)::_23_957 -> begin
(match ((let _68_9205 = (unmeta_exp pats)
in _68_9205.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _23_978)); Microsoft_FStar_Absyn_Syntax.tk = _23_975; Microsoft_FStar_Absyn_Syntax.pos = _23_973; Microsoft_FStar_Absyn_Syntax.fvs = _23_971; Microsoft_FStar_Absyn_Syntax.uvs = _23_969}, _23_983)) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.cons_lid)
end
| _23_987 -> begin
false
end)
end
| _23_989 -> begin
false
end)
end
| _23_991 -> begin
false
end)
end
| _23_993 -> begin
false
end))

let is_ml_comp = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
((Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_ML_lid) || (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _23_20 ) -> (match (_23_20) with
| Microsoft_FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _23_1000 -> begin
false
end)))))
end
| _23_1002 -> begin
false
end))

let comp_result = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
ct.Microsoft_FStar_Absyn_Syntax.result_typ
end))

let set_result_typ = (fun ( c ) ( t ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (_23_1011) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Total t)
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Comp (let _23_1015 = ct
in {Microsoft_FStar_Absyn_Syntax.effect_name = _23_1015.Microsoft_FStar_Absyn_Syntax.effect_name; Microsoft_FStar_Absyn_Syntax.result_typ = t; Microsoft_FStar_Absyn_Syntax.effect_args = _23_1015.Microsoft_FStar_Absyn_Syntax.effect_args; Microsoft_FStar_Absyn_Syntax.flags = _23_1015.Microsoft_FStar_Absyn_Syntax.flags}))
end))

let is_trivial_wp = (fun ( c ) -> (Support.Prims.pipe_right (comp_flags c) (Support.Microsoft.FStar.Util.for_some (fun ( _23_21 ) -> (match (_23_21) with
| (Microsoft_FStar_Absyn_Syntax.TOTAL) | (Microsoft_FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _23_1022 -> begin
false
end)))))

let rec is_atom = (fun ( e ) -> (match ((let _68_9215 = (compress_exp e)
in _68_9215.Microsoft_FStar_Absyn_Syntax.n)) with
| (Microsoft_FStar_Absyn_Syntax.Exp_bvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) -> begin
true
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _23_1035))) -> begin
(is_atom e)
end
| _23_1040 -> begin
false
end))

let primops = (Microsoft_FStar_Absyn_Const.op_Eq)::(Microsoft_FStar_Absyn_Const.op_notEq)::(Microsoft_FStar_Absyn_Const.op_LT)::(Microsoft_FStar_Absyn_Const.op_LTE)::(Microsoft_FStar_Absyn_Const.op_GT)::(Microsoft_FStar_Absyn_Const.op_GTE)::(Microsoft_FStar_Absyn_Const.op_Subtraction)::(Microsoft_FStar_Absyn_Const.op_Minus)::(Microsoft_FStar_Absyn_Const.op_Addition)::(Microsoft_FStar_Absyn_Const.op_Multiply)::(Microsoft_FStar_Absyn_Const.op_Division)::(Microsoft_FStar_Absyn_Const.op_Modulus)::(Microsoft_FStar_Absyn_Const.op_And)::(Microsoft_FStar_Absyn_Const.op_Or)::(Microsoft_FStar_Absyn_Const.op_Negation)::[]

let is_primop = (fun ( f ) -> (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _23_1044)) -> begin
(Support.Prims.pipe_right primops (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v)))
end
| _23_1048 -> begin
false
end))

let rec unascribe = (fun ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _23_1052, _23_1054)) -> begin
(unascribe e)
end
| _23_1058 -> begin
e
end))

let rec ascribe_typ = (fun ( t ) ( k ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t', _23_1063)) -> begin
(ascribe_typ t' k)
end
| _23_1067 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.Microsoft_FStar_Absyn_Syntax.pos)
end))

let rec unascribe_typ = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _23_1071)) -> begin
(unascribe_typ t)
end
| _23_1075 -> begin
t
end))

let rec unrefine = (fun ( t ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _23_1080)) -> begin
(unrefine x.Microsoft_FStar_Absyn_Syntax.sort)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _23_1085)) -> begin
(unrefine t)
end
| _23_1089 -> begin
t
end)))

let is_fun = (fun ( e ) -> (match ((let _68_9229 = (compress_exp e)
in _68_9229.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_abs (_23_1092) -> begin
true
end
| _23_1095 -> begin
false
end))

let is_function_typ = (fun ( t ) -> (match ((let _68_9232 = (compress_typ t)
in _68_9232.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_23_1098) -> begin
true
end
| _23_1101 -> begin
false
end))

let rec pre_typ = (fun ( t ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, _23_1106)) -> begin
(pre_typ x.Microsoft_FStar_Absyn_Syntax.sort)
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _23_1111)) -> begin
(pre_typ t)
end
| _23_1115 -> begin
t
end)))

let destruct = (fun ( typ ) ( lid ) -> (let typ = (compress_typ typ)
in (match (typ.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _23_1126; Microsoft_FStar_Absyn_Syntax.pos = _23_1124; Microsoft_FStar_Absyn_Syntax.fvs = _23_1122; Microsoft_FStar_Absyn_Syntax.uvs = _23_1120}, args)) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v lid) -> begin
Some (args)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v lid) -> begin
Some ([])
end
| _23_1136 -> begin
None
end)))

let rec lids_of_sigelt = (fun ( se ) -> (match (se) with
| (Microsoft_FStar_Absyn_Syntax.Sig_let ((_, _, lids, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_bundle ((_, _, lids, _))) -> begin
lids
end
| (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, _, _, _, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((lid, _, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, _, _, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, _, _, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((lid, _, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, _, _, _))) -> begin
(lid)::[]
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((n, _23_1230)) -> begin
(n.Microsoft_FStar_Absyn_Syntax.mname)::[]
end
| (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_main (_)) -> begin
[]
end))

let lid_of_sigelt = (fun ( se ) -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _23_1246 -> begin
None
end))

let range_of_sigelt = (fun ( x ) -> (match (x) with
| (Microsoft_FStar_Absyn_Syntax.Sig_bundle ((_, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_tycon ((_, _, _, _, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((_, _, _, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((_, _, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_datacon ((_, _, _, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((_, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_assume ((_, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_let ((_, r, _, _))) | (Microsoft_FStar_Absyn_Syntax.Sig_main ((_, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_pragma ((_, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect ((_, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev ((_, _, _, r))) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect ((_, r))) -> begin
r
end))

let range_of_lb = (fun ( _23_22 ) -> (match (_23_22) with
| (Support.Microsoft.FStar.Util.Inl (x), _23_1357, _23_1359) -> begin
(range_of_bvd x)
end
| (Support.Microsoft.FStar.Util.Inr (l), _23_1364, _23_1366) -> begin
(Microsoft_FStar_Absyn_Syntax.range_of_lid l)
end))

let range_of_arg = (fun ( _23_23 ) -> (match (_23_23) with
| (Support.Microsoft.FStar.Util.Inl (hd), _23_1372) -> begin
hd.Microsoft_FStar_Absyn_Syntax.pos
end
| (Support.Microsoft.FStar.Util.Inr (hd), _23_1377) -> begin
hd.Microsoft_FStar_Absyn_Syntax.pos
end))

let range_of_args = (fun ( args ) ( r ) -> (Support.Prims.pipe_right args (Support.List.fold_left (fun ( r ) ( a ) -> (Support.Microsoft.FStar.Range.union_ranges r (range_of_arg a))) r)))

let mk_typ_app = (fun ( f ) ( args ) -> (let r = (range_of_args args f.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app (f, args) None r)))

let mk_exp_app = (fun ( f ) ( args ) -> (let r = (range_of_args args f.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app (f, args) None r)))

let mk_data = (fun ( l ) ( args ) -> (match (args) with
| [] -> begin
(let _68_9266 = (let _68_9265 = (let _68_9264 = (let _68_9263 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) l _68_9263))
in (_68_9264, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_68_9265))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _68_9266))
end
| _23_1393 -> begin
(let _68_9271 = (let _68_9270 = (let _68_9269 = (let _68_9268 = (let _68_9267 = (Microsoft_FStar_Absyn_Syntax.range_of_lid l)
in (fvar (Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) l _68_9267))
in (mk_exp_app _68_9268 args))
in (_68_9269, Microsoft_FStar_Absyn_Syntax.Data_app))
in Microsoft_FStar_Absyn_Syntax.Meta_desugared (_68_9270))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_meta _68_9271))
end))

let mangle_field_name = (fun ( x ) -> (Microsoft_FStar_Absyn_Syntax.mk_ident ((Support.String.strcat "^fname^" x.Microsoft_FStar_Absyn_Syntax.idText), x.Microsoft_FStar_Absyn_Syntax.idRange)))

let unmangle_field_name = (fun ( x ) -> (match ((Support.Microsoft.FStar.Util.starts_with x.Microsoft_FStar_Absyn_Syntax.idText "^fname^")) with
| true -> begin
(let _68_9277 = (let _68_9276 = (Support.Microsoft.FStar.Util.substring_from x.Microsoft_FStar_Absyn_Syntax.idText 7)
in (_68_9276, x.Microsoft_FStar_Absyn_Syntax.idRange))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _68_9277))
end
| false -> begin
x
end))

let mk_field_projector_name = (fun ( lid ) ( x ) ( i ) -> (let nm = (match ((Microsoft_FStar_Absyn_Syntax.is_null_bvar x)) with
| true -> begin
(let _68_9283 = (let _68_9282 = (let _68_9281 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.String.strcat "_" _68_9281))
in (_68_9282, x.Microsoft_FStar_Absyn_Syntax.p))
in (Microsoft_FStar_Absyn_Syntax.mk_ident _68_9283))
end
| false -> begin
x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname
end)
in (let y = (let _23_1402 = x.Microsoft_FStar_Absyn_Syntax.v
in {Microsoft_FStar_Absyn_Syntax.ppname = nm; Microsoft_FStar_Absyn_Syntax.realname = _23_1402.Microsoft_FStar_Absyn_Syntax.realname})
in (let _68_9288 = (let _68_9287 = (let _68_9286 = (Microsoft_FStar_Absyn_Syntax.ids_of_lid lid)
in (let _68_9285 = (let _68_9284 = (unmangle_field_name nm)
in (_68_9284)::[])
in (Support.List.append _68_9286 _68_9285)))
in (Microsoft_FStar_Absyn_Syntax.lid_of_ids _68_9287))
in (_68_9288, y)))))

let unchecked_unify = (fun ( uv ) ( t ) -> (match ((Support.Microsoft.FStar.Unionfind.find uv)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (_23_1408) -> begin
(let _68_9293 = (let _68_9292 = (let _68_9291 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_int _68_9291))
in (Support.Microsoft.FStar.Util.format1 "Changing a fixed uvar! U%s\n" _68_9292))
in (failwith (_68_9293)))
end
| _23_1411 -> begin
(Support.Microsoft.FStar.Unionfind.change uv (Microsoft_FStar_Absyn_Syntax.Fixed (t)))
end))

type bvars =
(Microsoft_FStar_Absyn_Syntax.btvar Support.Microsoft.FStar.Util.set * Microsoft_FStar_Absyn_Syntax.bvvar Support.Microsoft.FStar.Util.set)

let no_bvars = (Microsoft_FStar_Absyn_Syntax.no_fvs.Microsoft_FStar_Absyn_Syntax.ftvs, Microsoft_FStar_Absyn_Syntax.no_fvs.Microsoft_FStar_Absyn_Syntax.fxvs)

let fvs_included = (fun ( fvs1 ) ( fvs2 ) -> ((Support.Microsoft.FStar.Util.set_is_subset_of fvs1.Microsoft_FStar_Absyn_Syntax.ftvs fvs2.Microsoft_FStar_Absyn_Syntax.ftvs) && (Support.Microsoft.FStar.Util.set_is_subset_of fvs1.Microsoft_FStar_Absyn_Syntax.fxvs fvs2.Microsoft_FStar_Absyn_Syntax.fxvs)))

let eq_fvars = (fun ( v1 ) ( v2 ) -> (match ((v1, v2)) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq a b)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x y)
end
| _23_1427 -> begin
false
end))

let eq_binder = (fun ( b1 ) ( b2 ) -> (match (((Support.Prims.fst b1), (Support.Prims.fst b2))) with
| (Support.Microsoft.FStar.Util.Inl (x), Support.Microsoft.FStar.Util.Inl (y)) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Microsoft_FStar_Absyn_Syntax.bvd_eq x.Microsoft_FStar_Absyn_Syntax.v y.Microsoft_FStar_Absyn_Syntax.v)
end
| _23_1441 -> begin
false
end))

let uv_eq = (fun ( _23_1445 ) ( _23_1449 ) -> (match ((_23_1445, _23_1449)) with
| ((uv1, _23_1444), (uv2, _23_1448)) -> begin
(Support.Microsoft.FStar.Unionfind.equivalent uv1 uv2)
end))

let union_uvs = (fun ( uvs1 ) ( uvs2 ) -> (let _68_9322 = (Support.Microsoft.FStar.Util.set_union uvs1.Microsoft_FStar_Absyn_Syntax.uvars_k uvs2.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (let _68_9321 = (Support.Microsoft.FStar.Util.set_union uvs1.Microsoft_FStar_Absyn_Syntax.uvars_t uvs2.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (let _68_9320 = (Support.Microsoft.FStar.Util.set_union uvs1.Microsoft_FStar_Absyn_Syntax.uvars_e uvs2.Microsoft_FStar_Absyn_Syntax.uvars_e)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _68_9322; Microsoft_FStar_Absyn_Syntax.uvars_t = _68_9321; Microsoft_FStar_Absyn_Syntax.uvars_e = _68_9320}))))

let union_fvs = (fun ( fvs1 ) ( fvs2 ) -> (let _68_9328 = (Support.Microsoft.FStar.Util.set_union fvs1.Microsoft_FStar_Absyn_Syntax.ftvs fvs2.Microsoft_FStar_Absyn_Syntax.ftvs)
in (let _68_9327 = (Support.Microsoft.FStar.Util.set_union fvs1.Microsoft_FStar_Absyn_Syntax.fxvs fvs2.Microsoft_FStar_Absyn_Syntax.fxvs)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _68_9328; Microsoft_FStar_Absyn_Syntax.fxvs = _68_9327})))

let union_fvs_uvs = (fun ( _23_1456 ) ( _23_1459 ) -> (match ((_23_1456, _23_1459)) with
| ((fvs1, uvs1), (fvs2, uvs2)) -> begin
(let _68_9334 = (union_fvs fvs1 fvs2)
in (let _68_9333 = (union_uvs uvs1 uvs2)
in (_68_9334, _68_9333)))
end))

let sub_fv = (fun ( _23_1462 ) ( _23_1465 ) -> (match ((_23_1462, _23_1465)) with
| ((fvs, uvs), (tvars, vvars)) -> begin
(let _68_9355 = (let _23_1466 = fvs
in (let _68_9354 = (Support.Microsoft.FStar.Util.set_difference fvs.Microsoft_FStar_Absyn_Syntax.ftvs tvars)
in (let _68_9353 = (Support.Microsoft.FStar.Util.set_difference fvs.Microsoft_FStar_Absyn_Syntax.fxvs vvars)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _68_9354; Microsoft_FStar_Absyn_Syntax.fxvs = _68_9353})))
in (_68_9355, uvs))
end))

let stash = (fun ( uvonly ) ( s ) ( _23_1474 ) -> (match (_23_1474) with
| (fvs, uvs) -> begin
(let _23_1475 = (Support.ST.op_Colon_Equals s.Microsoft_FStar_Absyn_Syntax.uvs (Some (uvs)))
in (match (uvonly) with
| true -> begin
()
end
| false -> begin
(Support.ST.op_Colon_Equals s.Microsoft_FStar_Absyn_Syntax.fvs (Some (fvs)))
end))
end))

let single_fv = (fun ( x ) -> (let _68_9366 = (Microsoft_FStar_Absyn_Syntax.new_ftv_set ())
in (Support.Microsoft.FStar.Util.set_add x _68_9366)))

let single_uv = (fun ( u ) -> (let _68_9374 = (Microsoft_FStar_Absyn_Syntax.new_uv_set ())
in (Support.Microsoft.FStar.Util.set_add u _68_9374)))

let single_uvt = (fun ( u ) -> (let _68_9382 = (Microsoft_FStar_Absyn_Syntax.new_uvt_set ())
in (Support.Microsoft.FStar.Util.set_add u _68_9382)))

let rec vs_typ' = (fun ( t ) ( uvonly ) ( cont ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_23_1486) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| false -> begin
(let _68_9497 = (let _68_9496 = (let _23_1490 = Microsoft_FStar_Absyn_Syntax.no_fvs
in (let _68_9495 = (single_fv a)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _68_9495; Microsoft_FStar_Absyn_Syntax.fxvs = _23_1490.Microsoft_FStar_Absyn_Syntax.fxvs}))
in (_68_9496, Microsoft_FStar_Absyn_Syntax.no_uvs))
in (cont _68_9497))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(let _68_9500 = (let _68_9499 = (let _23_1496 = Microsoft_FStar_Absyn_Syntax.no_uvs
in (let _68_9498 = (single_uvt (uv, k))
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _23_1496.Microsoft_FStar_Absyn_Syntax.uvars_k; Microsoft_FStar_Absyn_Syntax.uvars_t = _68_9498; Microsoft_FStar_Absyn_Syntax.uvars_e = _23_1496.Microsoft_FStar_Absyn_Syntax.uvars_e}))
in (Microsoft_FStar_Absyn_Syntax.no_fvs, _68_9499))
in (cont _68_9500))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_unknown) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
(vs_binders bs uvonly (fun ( _23_1508 ) -> (match (_23_1508) with
| (bvs, vs1) -> begin
(vs_comp c uvonly (fun ( vs2 ) -> (let _68_9504 = (let _68_9503 = (union_fvs_uvs vs1 vs2)
in (sub_fv _68_9503 bvs))
in (cont _68_9504))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, t)) -> begin
(vs_binders bs uvonly (fun ( _23_1516 ) -> (match (_23_1516) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun ( vs2 ) -> (let _68_9508 = (let _68_9507 = (union_fvs_uvs vs1 vs2)
in (sub_fv _68_9507 bvs))
in (cont _68_9508))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, t)) -> begin
(vs_binders (((Support.Microsoft.FStar.Util.Inr (x), None))::[]) uvonly (fun ( _23_1524 ) -> (match (_23_1524) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun ( vs2 ) -> (let _68_9512 = (let _68_9511 = (union_fvs_uvs vs1 vs2)
in (sub_fv _68_9511 bvs))
in (cont _68_9512))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, args)) -> begin
(vs_typ t uvonly (fun ( vs1 ) -> (vs_args args uvonly (fun ( vs2 ) -> (let _68_9515 = (union_fvs_uvs vs1 vs2)
in (cont _68_9515))))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _23_1534)) -> begin
(vs_typ t uvonly cont)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, _23_1540))) -> begin
(vs_typ t1 uvonly (fun ( vs1 ) -> (vs_typ t2 uvonly (fun ( vs2 ) -> (let _68_9518 = (union_fvs_uvs vs1 vs2)
in (cont _68_9518))))))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, _, _, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, _)))) -> begin
(vs_typ t uvonly cont)
end)))
and vs_binders = (fun ( bs ) ( uvonly ) ( cont ) -> (match (bs) with
| [] -> begin
(cont (no_bvars, (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs)))
end
| (Support.Microsoft.FStar.Util.Inl (a), _23_1582)::rest -> begin
(vs_kind a.Microsoft_FStar_Absyn_Syntax.sort uvonly (fun ( vs ) -> (vs_binders rest uvonly (fun ( _23_1590 ) -> (match (_23_1590) with
| ((tvars, vvars), vs2) -> begin
(let _68_9555 = (let _68_9554 = (let _68_9552 = (Support.Microsoft.FStar.Util.set_add a tvars)
in (_68_9552, vvars))
in (let _68_9553 = (union_fvs_uvs vs vs2)
in (_68_9554, _68_9553)))
in (cont _68_9555))
end)))))
end
| (Support.Microsoft.FStar.Util.Inr (x), _23_1595)::rest -> begin
(vs_typ x.Microsoft_FStar_Absyn_Syntax.sort uvonly (fun ( vs ) -> (vs_binders rest uvonly (fun ( _23_1603 ) -> (match (_23_1603) with
| ((tvars, vvars), vs2) -> begin
(let _68_9579 = (let _68_9578 = (let _68_9576 = (Support.Microsoft.FStar.Util.set_add x vvars)
in (tvars, _68_9576))
in (let _68_9577 = (union_fvs_uvs vs vs2)
in (_68_9578, _68_9577)))
in (cont _68_9579))
end)))))
end))
and vs_args = (fun ( args ) ( uvonly ) ( cont ) -> (match (args) with
| [] -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| (Support.Microsoft.FStar.Util.Inl (t), _23_1613)::tl -> begin
(vs_typ t uvonly (fun ( ft1 ) -> (vs_args tl uvonly (fun ( ft2 ) -> (let _68_9583 = (union_fvs_uvs ft1 ft2)
in (cont _68_9583))))))
end
| (Support.Microsoft.FStar.Util.Inr (e), _23_1622)::tl -> begin
(vs_exp e uvonly (fun ( ft1 ) -> (vs_args tl uvonly (fun ( ft2 ) -> (let _68_9586 = (union_fvs_uvs ft1 ft2)
in (cont _68_9586))))))
end))
and vs_typ = (fun ( t ) ( uvonly ) ( cont ) -> (match ((let _68_9589 = (Support.ST.read t.Microsoft_FStar_Absyn_Syntax.fvs)
in (let _68_9588 = (Support.ST.read t.Microsoft_FStar_Absyn_Syntax.uvs)
in (_68_9589, _68_9588)))) with
| (Some (_23_1632), None) -> begin
(failwith ("Impossible"))
end
| (None, None) -> begin
(vs_typ' t uvonly (fun ( fvs ) -> (let _23_1640 = (stash uvonly t fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, uvs))
end
| false -> begin
(vs_typ' t uvonly (fun ( fvs ) -> (let _23_1647 = (stash uvonly t fvs)
in (cont fvs))))
end)
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_kind' = (fun ( k ) ( uvonly ) ( cont ) -> (let k = (compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam ((_23_1660, k)) -> begin
(let _68_9594 = (let _68_9593 = (Support.Microsoft.FStar.Range.string_of_range k.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Microsoft.FStar.Util.format1 "%s: Impossible ... found a Kind_lam bare" _68_9593))
in (failwith (_68_9594)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_23_1665) -> begin
(failwith ("Impossible"))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_unknown) | (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, args)) -> begin
(vs_args args uvonly (fun ( _23_1676 ) -> (match (_23_1676) with
| (fvs, uvs) -> begin
(let _68_9598 = (let _68_9597 = (let _23_1677 = uvs
in (let _68_9596 = (Support.Microsoft.FStar.Util.set_add uv uvs.Microsoft_FStar_Absyn_Syntax.uvars_k)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _68_9596; Microsoft_FStar_Absyn_Syntax.uvars_t = _23_1677.Microsoft_FStar_Absyn_Syntax.uvars_t; Microsoft_FStar_Absyn_Syntax.uvars_e = _23_1677.Microsoft_FStar_Absyn_Syntax.uvars_e}))
in (fvs, _68_9597))
in (cont _68_9598))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_23_1680, k)) -> begin
(vs_kind k uvonly cont)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(vs_binders bs uvonly (fun ( _23_1690 ) -> (match (_23_1690) with
| (bvs, vs1) -> begin
(vs_kind k uvonly (fun ( vs2 ) -> (let _68_9602 = (let _68_9601 = (union_fvs_uvs vs1 vs2)
in (sub_fv _68_9601 bvs))
in (cont _68_9602))))
end)))
end)))
and vs_kind = (fun ( k ) ( uvonly ) ( cont ) -> (match ((let _68_9605 = (Support.ST.read k.Microsoft_FStar_Absyn_Syntax.fvs)
in (let _68_9604 = (Support.ST.read k.Microsoft_FStar_Absyn_Syntax.uvs)
in (_68_9605, _68_9604)))) with
| (Some (_23_1697), None) -> begin
(failwith ("Impossible"))
end
| (None, None) -> begin
(vs_kind' k uvonly (fun ( fvs ) -> (let _23_1705 = (stash uvonly k fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, uvs))
end
| false -> begin
(vs_kind' k uvonly (fun ( fvs ) -> (let _23_1712 = (stash uvonly k fvs)
in (cont fvs))))
end)
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_exp' = (fun ( e ) ( uvonly ) ( cont ) -> (let e = (compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_23_1725) -> begin
(failwith ("impossible"))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_fvar (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, t)) -> begin
(let _68_9611 = (let _68_9610 = (let _23_1737 = Microsoft_FStar_Absyn_Syntax.no_uvs
in (let _68_9609 = (single_uvt (uv, t))
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _23_1737.Microsoft_FStar_Absyn_Syntax.uvars_k; Microsoft_FStar_Absyn_Syntax.uvars_t = _23_1737.Microsoft_FStar_Absyn_Syntax.uvars_t; Microsoft_FStar_Absyn_Syntax.uvars_e = _68_9609}))
in (Microsoft_FStar_Absyn_Syntax.no_fvs, _68_9610))
in (cont _68_9611))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| false -> begin
(let _68_9614 = (let _68_9613 = (let _23_1741 = Microsoft_FStar_Absyn_Syntax.no_fvs
in (let _68_9612 = (single_fv x)
in {Microsoft_FStar_Absyn_Syntax.ftvs = _23_1741.Microsoft_FStar_Absyn_Syntax.ftvs; Microsoft_FStar_Absyn_Syntax.fxvs = _68_9612}))
in (_68_9613, Microsoft_FStar_Absyn_Syntax.no_uvs))
in (cont _68_9614))
end)
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _23_1745, _23_1747)) -> begin
(vs_exp e uvonly cont)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, e)) -> begin
(vs_binders bs uvonly (fun ( _23_1756 ) -> (match (_23_1756) with
| (bvs, vs1) -> begin
(vs_exp e uvonly (fun ( vs2 ) -> (let _68_9618 = (let _68_9617 = (union_fvs_uvs vs1 vs2)
in (sub_fv _68_9617 bvs))
in (cont _68_9618))))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((e, args)) -> begin
(vs_exp e uvonly (fun ( ft1 ) -> (vs_args args uvonly (fun ( ft2 ) -> (let _68_9621 = (union_fvs_uvs ft1 ft2)
in (cont _68_9621))))))
end
| (Microsoft_FStar_Absyn_Syntax.Exp_match (_)) | (Microsoft_FStar_Absyn_Syntax.Exp_let (_)) -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _23_1772))) -> begin
(vs_exp e uvonly cont)
end)))
and vs_exp = (fun ( e ) ( uvonly ) ( cont ) -> (match ((let _68_9624 = (Support.ST.read e.Microsoft_FStar_Absyn_Syntax.fvs)
in (let _68_9623 = (Support.ST.read e.Microsoft_FStar_Absyn_Syntax.uvs)
in (_68_9624, _68_9623)))) with
| (Some (_23_1781), None) -> begin
(failwith ("Impossible"))
end
| (None, None) -> begin
(vs_exp' e uvonly (fun ( fvs ) -> (let _23_1789 = (stash uvonly e fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, uvs))
end
| false -> begin
(vs_exp' e uvonly (fun ( fvs ) -> (let _23_1796 = (stash uvonly e fvs)
in (cont fvs))))
end)
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_comp' = (fun ( c ) ( uvonly ) ( k ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(vs_typ t uvonly k)
end
| Microsoft_FStar_Absyn_Syntax.Comp (ct) -> begin
(match (uvonly) with
| true -> begin
(vs_typ ct.Microsoft_FStar_Absyn_Syntax.result_typ uvonly k)
end
| false -> begin
(vs_typ ct.Microsoft_FStar_Absyn_Syntax.result_typ uvonly (fun ( vs1 ) -> (vs_args ct.Microsoft_FStar_Absyn_Syntax.effect_args uvonly (fun ( vs2 ) -> (let _68_9630 = (union_fvs_uvs vs1 vs2)
in (k _68_9630))))))
end)
end))
and vs_comp = (fun ( c ) ( uvonly ) ( cont ) -> (match ((let _68_9633 = (Support.ST.read c.Microsoft_FStar_Absyn_Syntax.fvs)
in (let _68_9632 = (Support.ST.read c.Microsoft_FStar_Absyn_Syntax.uvs)
in (_68_9633, _68_9632)))) with
| (Some (_23_1818), None) -> begin
(failwith ("Impossible"))
end
| (None, None) -> begin
(vs_comp' c uvonly (fun ( fvs ) -> (let _23_1826 = (stash uvonly c fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
(match (uvonly) with
| true -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, uvs))
end
| false -> begin
(vs_comp' c uvonly (fun ( fvs ) -> (let _23_1833 = (stash uvonly c fvs)
in (cont fvs))))
end)
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_either = (fun ( te ) ( uvonly ) ( cont ) -> (match (te) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(vs_typ t uvonly cont)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(vs_exp e uvonly cont)
end))
and vs_either_l = (fun ( tes ) ( uvonly ) ( cont ) -> (match (tes) with
| [] -> begin
(cont (Microsoft_FStar_Absyn_Syntax.no_fvs, Microsoft_FStar_Absyn_Syntax.no_uvs))
end
| hd::tl -> begin
(vs_either hd uvonly (fun ( ft1 ) -> (vs_either_l tl uvonly (fun ( ft2 ) -> (let _68_9640 = (union_fvs_uvs ft1 ft2)
in (cont _68_9640))))))
end))

let freevars_kind = (fun ( k ) -> (vs_kind k false (fun ( _23_1862 ) -> (match (_23_1862) with
| (x, _23_1861) -> begin
x
end))))

let freevars_typ = (fun ( t ) -> (vs_typ t false (fun ( _23_1867 ) -> (match (_23_1867) with
| (x, _23_1866) -> begin
x
end))))

let freevars_exp = (fun ( e ) -> (vs_exp e false (fun ( _23_1872 ) -> (match (_23_1872) with
| (x, _23_1871) -> begin
x
end))))

let freevars_comp = (fun ( c ) -> (vs_comp c false (fun ( _23_1877 ) -> (match (_23_1877) with
| (x, _23_1876) -> begin
x
end))))

let freevars_args = (fun ( args ) -> (Support.Prims.pipe_right args (Support.List.fold_left (fun ( out ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _68_9656 = (freevars_typ t)
in (Support.Prims.pipe_left (union_fvs out) _68_9656))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _68_9657 = (freevars_exp e)
in (Support.Prims.pipe_left (union_fvs out) _68_9657))
end)) Microsoft_FStar_Absyn_Syntax.no_fvs)))

let is_free = (fun ( axs ) ( fvs ) -> (Support.Prims.pipe_right axs (Support.Microsoft.FStar.Util.for_some (fun ( _23_24 ) -> (match (_23_24) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(Support.Microsoft.FStar.Util.set_mem a fvs.Microsoft_FStar_Absyn_Syntax.ftvs)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(Support.Microsoft.FStar.Util.set_mem x fvs.Microsoft_FStar_Absyn_Syntax.fxvs)
end)))))

type syntax_sum =
| SynSumKind of Microsoft_FStar_Absyn_Syntax.knd
| SynSumType of Microsoft_FStar_Absyn_Syntax.typ
| SynSumExp of Microsoft_FStar_Absyn_Syntax.exp
| SynSumComp of (Microsoft_FStar_Absyn_Syntax.comp', unit) Microsoft_FStar_Absyn_Syntax.syntax

let is_SynSumKind = (fun ( _discr_ ) -> (match (_discr_) with
| SynSumKind (_) -> begin
true
end
| _ -> begin
false
end))

let is_SynSumType = (fun ( _discr_ ) -> (match (_discr_) with
| SynSumType (_) -> begin
true
end
| _ -> begin
false
end))

let is_SynSumExp = (fun ( _discr_ ) -> (match (_discr_) with
| SynSumExp (_) -> begin
true
end
| _ -> begin
false
end))

let is_SynSumComp = (fun ( _discr_ ) -> (match (_discr_) with
| SynSumComp (_) -> begin
true
end
| _ -> begin
false
end))

let rec update_uvars = (fun ( s ) ( uvs ) -> (let out = (let _68_9703 = (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_k)
in (Support.Prims.pipe_right _68_9703 (Support.List.fold_left (fun ( out ) ( u ) -> (match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (k) -> begin
(let _68_9701 = (uvars_in_kind k)
in (union_uvs _68_9701 out))
end
| _23_1907 -> begin
(let _23_1908 = out
in (let _68_9702 = (Support.Microsoft.FStar.Util.set_add u out.Microsoft_FStar_Absyn_Syntax.uvars_k)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _68_9702; Microsoft_FStar_Absyn_Syntax.uvars_t = _23_1908.Microsoft_FStar_Absyn_Syntax.uvars_t; Microsoft_FStar_Absyn_Syntax.uvars_e = _23_1908.Microsoft_FStar_Absyn_Syntax.uvars_e}))
end)) Microsoft_FStar_Absyn_Syntax.no_uvs)))
in (let out = (let _68_9708 = (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_t)
in (Support.Prims.pipe_right _68_9708 (Support.List.fold_left (fun ( out ) ( _23_1914 ) -> (match (_23_1914) with
| (u, t) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (t) -> begin
(let _68_9706 = (uvars_in_typ t)
in (union_uvs _68_9706 out))
end
| _23_1918 -> begin
(let _23_1919 = out
in (let _68_9707 = (Support.Microsoft.FStar.Util.set_add (u, t) out.Microsoft_FStar_Absyn_Syntax.uvars_t)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _23_1919.Microsoft_FStar_Absyn_Syntax.uvars_k; Microsoft_FStar_Absyn_Syntax.uvars_t = _68_9707; Microsoft_FStar_Absyn_Syntax.uvars_e = _23_1919.Microsoft_FStar_Absyn_Syntax.uvars_e}))
end)
end)) out)))
in (let out = (let _68_9713 = (Support.Microsoft.FStar.Util.set_elements uvs.Microsoft_FStar_Absyn_Syntax.uvars_e)
in (Support.Prims.pipe_right _68_9713 (Support.List.fold_left (fun ( out ) ( _23_1925 ) -> (match (_23_1925) with
| (u, t) -> begin
(match ((Support.Microsoft.FStar.Unionfind.find u)) with
| Microsoft_FStar_Absyn_Syntax.Fixed (e) -> begin
(let _68_9711 = (uvars_in_exp e)
in (union_uvs _68_9711 out))
end
| _23_1929 -> begin
(let _23_1930 = out
in (let _68_9712 = (Support.Microsoft.FStar.Util.set_add (u, t) out.Microsoft_FStar_Absyn_Syntax.uvars_e)
in {Microsoft_FStar_Absyn_Syntax.uvars_k = _23_1930.Microsoft_FStar_Absyn_Syntax.uvars_k; Microsoft_FStar_Absyn_Syntax.uvars_t = _23_1930.Microsoft_FStar_Absyn_Syntax.uvars_t; Microsoft_FStar_Absyn_Syntax.uvars_e = _68_9712}))
end)
end)) out)))
in (let _23_1941 = (match (s) with
| SynSumKind (k) -> begin
(Support.ST.op_Colon_Equals k.Microsoft_FStar_Absyn_Syntax.uvs (Some (out)))
end
| SynSumType (t) -> begin
(Support.ST.op_Colon_Equals t.Microsoft_FStar_Absyn_Syntax.uvs (Some (out)))
end
| SynSumExp (e) -> begin
(Support.ST.op_Colon_Equals e.Microsoft_FStar_Absyn_Syntax.uvs (Some (out)))
end
| SynSumComp (c) -> begin
(Support.ST.op_Colon_Equals c.Microsoft_FStar_Absyn_Syntax.uvs (Some (out)))
end)
in out)))))
and uvars_in_kind = (fun ( k ) -> (let _68_9716 = (vs_kind k true (fun ( _23_1947 ) -> (match (_23_1947) with
| (_23_1945, x) -> begin
x
end)))
in (Support.Prims.pipe_left (update_uvars (SynSumKind (k))) _68_9716)))
and uvars_in_typ = (fun ( t ) -> (let _68_9719 = (vs_typ t true (fun ( _23_1952 ) -> (match (_23_1952) with
| (_23_1950, x) -> begin
x
end)))
in (Support.Prims.pipe_left (update_uvars (SynSumType (t))) _68_9719)))
and uvars_in_exp = (fun ( e ) -> (let _68_9722 = (vs_exp e true (fun ( _23_1957 ) -> (match (_23_1957) with
| (_23_1955, x) -> begin
x
end)))
in (Support.Prims.pipe_left (update_uvars (SynSumExp (e))) _68_9722)))
and uvars_in_comp = (fun ( c ) -> (let _68_9725 = (vs_comp c true (fun ( _23_1962 ) -> (match (_23_1962) with
| (_23_1960, x) -> begin
x
end)))
in (Support.Prims.pipe_left (update_uvars (SynSumComp (c))) _68_9725)))

let uvars_included_in = (fun ( u1 ) ( u2 ) -> (((Support.Microsoft.FStar.Util.set_is_subset_of u1.Microsoft_FStar_Absyn_Syntax.uvars_k u2.Microsoft_FStar_Absyn_Syntax.uvars_k) && (Support.Microsoft.FStar.Util.set_is_subset_of u1.Microsoft_FStar_Absyn_Syntax.uvars_t u2.Microsoft_FStar_Absyn_Syntax.uvars_t)) && (Support.Microsoft.FStar.Util.set_is_subset_of u1.Microsoft_FStar_Absyn_Syntax.uvars_e u2.Microsoft_FStar_Absyn_Syntax.uvars_e)))

let rec kind_formals = (fun ( k ) -> (let k = (compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam (_23_1968) -> begin
(failwith ("Impossible"))
end
| (Microsoft_FStar_Absyn_Syntax.Kind_unknown) | (Microsoft_FStar_Absyn_Syntax.Kind_type) | (Microsoft_FStar_Absyn_Syntax.Kind_effect) | (Microsoft_FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
([], k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _23_1982 = (kind_formals k)
in (match (_23_1982) with
| (bs', k) -> begin
((Support.List.append bs bs'), k)
end))
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_23_1984, k)) -> begin
(kind_formals k)
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_23_1989) -> begin
(failwith ("Impossible"))
end)))

let close_for_kind = (fun ( t ) ( k ) -> (let _23_1996 = (kind_formals k)
in (match (_23_1996) with
| (bs, _23_1995) -> begin
(match (bs) with
| [] -> begin
t
end
| _23_1999 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.Microsoft_FStar_Absyn_Syntax.pos)
end)
end)))

let rec unabbreviate_kind = (fun ( k ) -> (let k = (compress_kind k)
in (match (k.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_23_2003, k)) -> begin
(unabbreviate_kind k)
end
| _23_2008 -> begin
k
end)))

let close_with_lam = (fun ( tps ) ( t ) -> (match (tps) with
| [] -> begin
t
end
| _23_2013 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (tps, t) None t.Microsoft_FStar_Absyn_Syntax.pos)
end))

let close_with_arrow = (fun ( tps ) ( t ) -> (match (tps) with
| [] -> begin
t
end
| _23_2018 -> begin
(let _23_2027 = (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs', c)) -> begin
((Support.List.append tps bs'), c)
end
| _23_2024 -> begin
(let _68_9746 = (Microsoft_FStar_Absyn_Syntax.mk_Total t)
in (tps, _68_9746))
end)
in (match (_23_2027) with
| (bs, c) -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.Microsoft_FStar_Absyn_Syntax.pos)
end))
end))

let close_typ = close_with_arrow

let close_kind = (fun ( tps ) ( k ) -> (match (tps) with
| [] -> begin
k
end
| _23_2032 -> begin
(Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow' (tps, k) k.Microsoft_FStar_Absyn_Syntax.pos)
end))

let is_tuple_constructor = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (l) -> begin
(Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str "Prims.Tuple")
end
| _23_2037 -> begin
false
end))

let mk_tuple_lid = (fun ( n ) ( r ) -> (let t = (let _68_9759 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "Tuple%s" _68_9759))
in (let _68_9760 = (Microsoft_FStar_Absyn_Const.pconst t)
in (set_lid_range _68_9760 r))))

let mk_tuple_data_lid = (fun ( n ) ( r ) -> (let t = (let _68_9765 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "MkTuple%s" _68_9765))
in (let _68_9766 = (Microsoft_FStar_Absyn_Const.pconst t)
in (set_lid_range _68_9766 r))))

let is_tuple_data_lid = (fun ( f ) ( n ) -> (let _68_9771 = (mk_tuple_data_lid n Microsoft_FStar_Absyn_Syntax.dummyRange)
in (Microsoft_FStar_Absyn_Syntax.lid_equals f _68_9771)))

let is_dtuple_constructor = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (l) -> begin
(Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str "Prims.DTuple")
end
| _23_2050 -> begin
false
end))

let mk_dtuple_lid = (fun ( n ) ( r ) -> (let t = (let _68_9778 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "DTuple%s" _68_9778))
in (let _68_9779 = (Microsoft_FStar_Absyn_Const.pconst t)
in (set_lid_range _68_9779 r))))

let mk_dtuple_data_lid = (fun ( n ) ( r ) -> (let t = (let _68_9784 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "MkDTuple%s" _68_9784))
in (let _68_9785 = (Microsoft_FStar_Absyn_Const.pconst t)
in (set_lid_range _68_9785 r))))

let is_lid_equality = (fun ( x ) -> ((((Microsoft_FStar_Absyn_Syntax.lid_equals x Microsoft_FStar_Absyn_Const.eq_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals x Microsoft_FStar_Absyn_Const.eq2_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals x Microsoft_FStar_Absyn_Const.eqA_lid)) || (Microsoft_FStar_Absyn_Syntax.lid_equals x Microsoft_FStar_Absyn_Const.eqT_lid)))

let is_forall = (fun ( lid ) -> ((Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.forall_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.allTyp_lid)))

let is_exists = (fun ( lid ) -> ((Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.exists_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.exTyp_lid)))

let is_qlid = (fun ( lid ) -> ((is_forall lid) || (is_exists lid)))

let is_equality = (fun ( x ) -> (is_lid_equality x.Microsoft_FStar_Absyn_Syntax.v))

let lid_is_connective = (let lst = (Microsoft_FStar_Absyn_Const.and_lid)::(Microsoft_FStar_Absyn_Const.or_lid)::(Microsoft_FStar_Absyn_Const.not_lid)::(Microsoft_FStar_Absyn_Const.iff_lid)::(Microsoft_FStar_Absyn_Const.imp_lid)::[]
in (fun ( lid ) -> (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals lid) lst)))

let is_constructor = (fun ( t ) ( lid ) -> (match ((let _68_9801 = (pre_typ t)
in _68_9801.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v lid)
end
| _23_2069 -> begin
false
end))

let rec is_constructed_typ = (fun ( t ) ( lid ) -> (match ((let _68_9806 = (pre_typ t)
in _68_9806.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (_23_2073) -> begin
(is_constructor t lid)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, _23_2077)) -> begin
(is_constructed_typ t lid)
end
| _23_2081 -> begin
false
end))

let rec get_tycon = (fun ( t ) -> (let t = (pre_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_const (_)) -> begin
Some (t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, _23_2092)) -> begin
(get_tycon t)
end
| _23_2096 -> begin
None
end)))

let base_kind = (fun ( _23_25 ) -> (match (_23_25) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
true
end
| _23_2100 -> begin
false
end))

let sortByFieldName = (fun ( fn_a_l ) -> (Support.Prims.pipe_right fn_a_l (Support.List.sortWith (fun ( _23_2106 ) ( _23_2110 ) -> (match ((_23_2106, _23_2110)) with
| ((fn1, _23_2105), (fn2, _23_2109)) -> begin
(let _68_9815 = (Microsoft_FStar_Absyn_Syntax.text_of_lid fn1)
in (let _68_9814 = (Microsoft_FStar_Absyn_Syntax.text_of_lid fn2)
in (Support.String.compare _68_9815 _68_9814)))
end)))))

let kt_kt = (Microsoft_FStar_Absyn_Const.kunary Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype)

let kt_kt_kt = (Microsoft_FStar_Absyn_Const.kbin Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype Microsoft_FStar_Absyn_Syntax.ktype)

let tand = (ftv Microsoft_FStar_Absyn_Const.and_lid kt_kt_kt)

let tor = (ftv Microsoft_FStar_Absyn_Const.or_lid kt_kt_kt)

let timp = (ftv Microsoft_FStar_Absyn_Const.imp_lid kt_kt_kt)

let tiff = (ftv Microsoft_FStar_Absyn_Const.iff_lid kt_kt_kt)

let t_bool = (ftv Microsoft_FStar_Absyn_Const.bool_lid Microsoft_FStar_Absyn_Syntax.ktype)

let t_false = (ftv Microsoft_FStar_Absyn_Const.false_lid Microsoft_FStar_Absyn_Syntax.ktype)

let t_true = (ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)

let b2t_v = (let _68_9819 = (let _68_9818 = (let _68_9817 = (let _68_9816 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.null_v_binder t_bool)
in (_68_9816)::[])
in (_68_9817, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_9818 Microsoft_FStar_Absyn_Syntax.dummyRange))
in (ftv Microsoft_FStar_Absyn_Const.b2t_lid _68_9819))

let mk_conj_opt = (fun ( phi1 ) ( phi2 ) -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _68_9830 = (let _68_9829 = (let _68_9827 = (let _68_9826 = (Microsoft_FStar_Absyn_Syntax.targ phi1)
in (let _68_9825 = (let _68_9824 = (Microsoft_FStar_Absyn_Syntax.targ phi2)
in (_68_9824)::[])
in (_68_9826)::_68_9825))
in (tand, _68_9827))
in (let _68_9828 = (Support.Microsoft.FStar.Range.union_ranges phi1.Microsoft_FStar_Absyn_Syntax.pos phi2.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_9829 None _68_9828)))
in Some (_68_9830))
end))

let mk_binop = (fun ( op_t ) ( phi1 ) ( phi2 ) -> (let _68_9842 = (let _68_9840 = (let _68_9839 = (Microsoft_FStar_Absyn_Syntax.targ phi1)
in (let _68_9838 = (let _68_9837 = (Microsoft_FStar_Absyn_Syntax.targ phi2)
in (_68_9837)::[])
in (_68_9839)::_68_9838))
in (op_t, _68_9840))
in (let _68_9841 = (Support.Microsoft.FStar.Range.union_ranges phi1.Microsoft_FStar_Absyn_Syntax.pos phi2.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_9842 None _68_9841))))

let mk_neg = (fun ( phi ) -> (let _68_9848 = (let _68_9847 = (ftv Microsoft_FStar_Absyn_Const.not_lid kt_kt)
in (let _68_9846 = (let _68_9845 = (Microsoft_FStar_Absyn_Syntax.targ phi)
in (_68_9845)::[])
in (_68_9847, _68_9846)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_9848 None phi.Microsoft_FStar_Absyn_Syntax.pos)))

let mk_conj = (fun ( phi1 ) ( phi2 ) -> (mk_binop tand phi1 phi2))

let mk_conj_l = (fun ( phi ) -> (match (phi) with
| [] -> begin
(ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
end
| hd::tl -> begin
(Support.List.fold_right mk_conj tl hd)
end))

let mk_disj = (fun ( phi1 ) ( phi2 ) -> (mk_binop tor phi1 phi2))

let mk_disj_l = (fun ( phi ) -> (match (phi) with
| [] -> begin
(ftv Microsoft_FStar_Absyn_Const.false_lid Microsoft_FStar_Absyn_Syntax.ktype)
end
| hd::tl -> begin
(Support.List.fold_right mk_disj tl hd)
end))

let mk_imp = (fun ( phi1 ) ( phi2 ) -> (match ((let _68_9865 = (compress_typ phi1)
in _68_9865.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.false_lid) -> begin
t_true
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) -> begin
phi2
end
| _23_2141 -> begin
(match ((let _68_9866 = (compress_typ phi2)
in _68_9866.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (tc) when ((Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.true_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals tc.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.false_lid)) -> begin
phi2
end
| _23_2145 -> begin
(mk_binop timp phi1 phi2)
end)
end))

let mk_iff = (fun ( phi1 ) ( phi2 ) -> (mk_binop tiff phi1 phi2))

let b2t = (fun ( e ) -> (let _68_9875 = (let _68_9874 = (let _68_9873 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.varg e)
in (_68_9873)::[])
in (b2t_v, _68_9874))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_9875 None e.Microsoft_FStar_Absyn_Syntax.pos)))

let rec unmeta_typ = (fun ( t ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, _, _, _)))) | (Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _, _)))) -> begin
(unmeta_typ t)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, _23_2185))) -> begin
(mk_conj t1 t2)
end
| _23_2190 -> begin
t
end)))

let eq_k = (let a = (let _68_9878 = (new_bvd None)
in (bvd_to_bvar_s _68_9878 Microsoft_FStar_Absyn_Syntax.ktype))
in (let atyp = (btvar_to_typ a)
in (let b = (let _68_9879 = (new_bvd None)
in (bvd_to_bvar_s _68_9879 Microsoft_FStar_Absyn_Syntax.ktype))
in (let btyp = (btvar_to_typ b)
in (let _68_9886 = (let _68_9885 = (let _68_9884 = (let _68_9883 = (let _68_9882 = (Microsoft_FStar_Absyn_Syntax.null_v_binder atyp)
in (let _68_9881 = (let _68_9880 = (Microsoft_FStar_Absyn_Syntax.null_v_binder btyp)
in (_68_9880)::[])
in (_68_9882)::_68_9881))
in ((Support.Microsoft.FStar.Util.Inl (b), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_68_9883)
in ((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_68_9884)
in (_68_9885, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_9886 Microsoft_FStar_Absyn_Syntax.dummyRange))))))

let teq = (ftv Microsoft_FStar_Absyn_Const.eq2_lid eq_k)

let mk_eq = (fun ( t1 ) ( t2 ) ( e1 ) ( e2 ) -> (match ((t1.Microsoft_FStar_Absyn_Syntax.n, t2.Microsoft_FStar_Absyn_Syntax.n)) with
| ((Microsoft_FStar_Absyn_Syntax.Typ_unknown, _)) | ((_, Microsoft_FStar_Absyn_Syntax.Typ_unknown)) -> begin
(failwith ("DIE! mk_eq with tun"))
end
| _23_2208 -> begin
(let _68_9904 = (let _68_9902 = (let _68_9901 = (Microsoft_FStar_Absyn_Syntax.itarg t1)
in (let _68_9900 = (let _68_9899 = (Microsoft_FStar_Absyn_Syntax.itarg t2)
in (let _68_9898 = (let _68_9897 = (Microsoft_FStar_Absyn_Syntax.varg e1)
in (let _68_9896 = (let _68_9895 = (Microsoft_FStar_Absyn_Syntax.varg e2)
in (_68_9895)::[])
in (_68_9897)::_68_9896))
in (_68_9899)::_68_9898))
in (_68_9901)::_68_9900))
in (teq, _68_9902))
in (let _68_9903 = (Support.Microsoft.FStar.Range.union_ranges e1.Microsoft_FStar_Absyn_Syntax.pos e2.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_9904 None _68_9903)))
end))

let eq_typ = (ftv Microsoft_FStar_Absyn_Const.eqT_lid Microsoft_FStar_Absyn_Syntax.kun)

let mk_eq_typ = (fun ( t1 ) ( t2 ) -> (let _68_9914 = (let _68_9912 = (let _68_9911 = (Microsoft_FStar_Absyn_Syntax.targ t1)
in (let _68_9910 = (let _68_9909 = (Microsoft_FStar_Absyn_Syntax.targ t2)
in (_68_9909)::[])
in (_68_9911)::_68_9910))
in (eq_typ, _68_9912))
in (let _68_9913 = (Support.Microsoft.FStar.Range.union_ranges t1.Microsoft_FStar_Absyn_Syntax.pos t2.Microsoft_FStar_Absyn_Syntax.pos)
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_9914 None _68_9913))))

let lex_t = (ftv Microsoft_FStar_Absyn_Const.lex_t_lid Microsoft_FStar_Absyn_Syntax.ktype)

let lex_top = (let lexnil = (withinfo Microsoft_FStar_Absyn_Const.lextop_lid lex_t Microsoft_FStar_Absyn_Syntax.dummyRange)
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar (lexnil, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) None Microsoft_FStar_Absyn_Syntax.dummyRange))

let lex_pair = (let a = (gen_bvar Microsoft_FStar_Absyn_Syntax.ktype)
in (let lexcons = (let _68_9924 = (let _68_9923 = (let _68_9922 = (let _68_9920 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (let _68_9919 = (let _68_9918 = (let _68_9915 = (btvar_to_typ a)
in (Microsoft_FStar_Absyn_Syntax.null_v_binder _68_9915))
in (let _68_9917 = (let _68_9916 = (Microsoft_FStar_Absyn_Syntax.null_v_binder lex_t)
in (_68_9916)::[])
in (_68_9918)::_68_9917))
in (_68_9920)::_68_9919))
in (let _68_9921 = (Microsoft_FStar_Absyn_Syntax.mk_Total lex_t)
in (_68_9922, _68_9921)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun _68_9923 None Microsoft_FStar_Absyn_Syntax.dummyRange))
in (withinfo Microsoft_FStar_Absyn_Const.lexcons_lid _68_9924 Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_fvar (lexcons, Some (Microsoft_FStar_Absyn_Syntax.Data_ctor)) None Microsoft_FStar_Absyn_Syntax.dummyRange)))

let forall_kind = (let a = (let _68_9925 = (new_bvd None)
in (bvd_to_bvar_s _68_9925 Microsoft_FStar_Absyn_Syntax.ktype))
in (let atyp = (btvar_to_typ a)
in (let _68_9933 = (let _68_9932 = (let _68_9931 = (let _68_9930 = (let _68_9929 = (let _68_9928 = (let _68_9927 = (let _68_9926 = (Microsoft_FStar_Absyn_Syntax.null_v_binder atyp)
in (_68_9926)::[])
in (_68_9927, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_9928 Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.null_t_binder _68_9929))
in (_68_9930)::[])
in ((Support.Microsoft.FStar.Util.Inl (a), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_68_9931)
in (_68_9932, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_9933 Microsoft_FStar_Absyn_Syntax.dummyRange))))

let tforall = (ftv Microsoft_FStar_Absyn_Const.forall_lid forall_kind)

let allT_k = (fun ( k ) -> (let _68_9942 = (let _68_9941 = (let _68_9940 = (let _68_9939 = (let _68_9938 = (let _68_9937 = (let _68_9936 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (_68_9936)::[])
in (_68_9937, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_9938 Microsoft_FStar_Absyn_Syntax.dummyRange))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.null_t_binder _68_9939))
in (_68_9940)::[])
in (_68_9941, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_9942 Microsoft_FStar_Absyn_Syntax.dummyRange)))

let eqT_k = (fun ( k ) -> (let _68_9949 = (let _68_9948 = (let _68_9947 = (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (let _68_9946 = (let _68_9945 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (_68_9945)::[])
in (_68_9947)::_68_9946))
in (_68_9948, Microsoft_FStar_Absyn_Syntax.ktype))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _68_9949 Microsoft_FStar_Absyn_Syntax.dummyRange)))

let tforall_typ = (fun ( k ) -> (let _68_9952 = (allT_k k)
in (ftv Microsoft_FStar_Absyn_Const.allTyp_lid _68_9952)))

let mk_forallT = (fun ( a ) ( b ) -> (let _68_9964 = (let _68_9963 = (tforall_typ a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _68_9962 = (let _68_9961 = (let _68_9960 = (let _68_9959 = (let _68_9958 = (let _68_9957 = (Microsoft_FStar_Absyn_Syntax.t_binder a)
in (_68_9957)::[])
in (_68_9958, b))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_9959 None b.Microsoft_FStar_Absyn_Syntax.pos))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_9960))
in (_68_9961)::[])
in (_68_9963, _68_9962)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_9964 None b.Microsoft_FStar_Absyn_Syntax.pos)))

let mk_forall = (fun ( x ) ( body ) -> (let r = Microsoft_FStar_Absyn_Syntax.dummyRange
in (let _68_9975 = (let _68_9974 = (let _68_9973 = (let _68_9972 = (let _68_9971 = (let _68_9970 = (let _68_9969 = (Microsoft_FStar_Absyn_Syntax.v_binder x)
in (_68_9969)::[])
in (_68_9970, body))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_9971 None r))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Syntax.targ _68_9972))
in (_68_9973)::[])
in (tforall, _68_9974))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_9975 None r))))

let rec close_forall = (fun ( bs ) ( f ) -> (Support.List.fold_right (fun ( b ) ( f ) -> (match ((Microsoft_FStar_Absyn_Syntax.is_null_binder b)) with
| true -> begin
f
end
| false -> begin
(let body = (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam ((b)::[], f) None f.Microsoft_FStar_Absyn_Syntax.pos)
in (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _68_9985 = (let _68_9984 = (tforall_typ a.Microsoft_FStar_Absyn_Syntax.sort)
in (let _68_9983 = (let _68_9982 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_68_9982)::[])
in (_68_9984, _68_9983)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_9985 None f.Microsoft_FStar_Absyn_Syntax.pos))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _68_9989 = (let _68_9988 = (let _68_9987 = (let _68_9986 = (Microsoft_FStar_Absyn_Syntax.targ body)
in (_68_9986)::[])
in ((Support.Microsoft.FStar.Util.Inl (x.Microsoft_FStar_Absyn_Syntax.sort), Some (Microsoft_FStar_Absyn_Syntax.Implicit)))::_68_9987)
in (tforall, _68_9988))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_app _68_9989 None f.Microsoft_FStar_Absyn_Syntax.pos))
end))
end)) bs f))

let rec is_wild_pat = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_wild (_23_2235) -> begin
true
end
| _23_2238 -> begin
false
end))

let head_and_args = (fun ( t ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(head, args)
end
| _23_2246 -> begin
(t, [])
end)))

let head_and_args_e = (fun ( e ) -> (let e = (compress_exp e)
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args)) -> begin
(head, args)
end
| _23_2254 -> begin
(e, [])
end)))

let function_formals = (fun ( t ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs, c)) -> begin
Some ((bs, c))
end
| _23_2262 -> begin
None
end)))

let is_interpreted = (fun ( l ) -> (let theory_syms = (Microsoft_FStar_Absyn_Const.op_Eq)::(Microsoft_FStar_Absyn_Const.op_notEq)::(Microsoft_FStar_Absyn_Const.op_LT)::(Microsoft_FStar_Absyn_Const.op_LTE)::(Microsoft_FStar_Absyn_Const.op_GT)::(Microsoft_FStar_Absyn_Const.op_GTE)::(Microsoft_FStar_Absyn_Const.op_Subtraction)::(Microsoft_FStar_Absyn_Const.op_Minus)::(Microsoft_FStar_Absyn_Const.op_Addition)::(Microsoft_FStar_Absyn_Const.op_Multiply)::(Microsoft_FStar_Absyn_Const.op_Division)::(Microsoft_FStar_Absyn_Const.op_Modulus)::(Microsoft_FStar_Absyn_Const.op_And)::(Microsoft_FStar_Absyn_Const.op_Or)::(Microsoft_FStar_Absyn_Const.op_Negation)::[]
in (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals l) theory_syms)))

type qpats =
Microsoft_FStar_Absyn_Syntax.args

type connective =
| QAll of (Microsoft_FStar_Absyn_Syntax.binders * qpats * Microsoft_FStar_Absyn_Syntax.typ)
| QEx of (Microsoft_FStar_Absyn_Syntax.binders * qpats * Microsoft_FStar_Absyn_Syntax.typ)
| BaseConn of (Microsoft_FStar_Absyn_Syntax.lident * Microsoft_FStar_Absyn_Syntax.args)

let is_QAll = (fun ( _discr_ ) -> (match (_discr_) with
| QAll (_) -> begin
true
end
| _ -> begin
false
end))

let is_QEx = (fun ( _discr_ ) -> (match (_discr_) with
| QEx (_) -> begin
true
end
| _ -> begin
false
end))

let is_BaseConn = (fun ( _discr_ ) -> (match (_discr_) with
| BaseConn (_) -> begin
true
end
| _ -> begin
false
end))

let destruct_typ_as_formula = (fun ( f ) -> (let destruct_base_conn = (fun ( f ) -> (let _23_2276 = (true, false)
in (match (_23_2276) with
| (type_sort, term_sort) -> begin
(let oneType = (type_sort)::[]
in (let twoTypes = (type_sort)::(type_sort)::[]
in (let threeTys = (type_sort)::(type_sort)::(type_sort)::[]
in (let twoTerms = (term_sort)::(term_sort)::[]
in (let connectives = ((Microsoft_FStar_Absyn_Const.true_lid, []))::((Microsoft_FStar_Absyn_Const.false_lid, []))::((Microsoft_FStar_Absyn_Const.and_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.or_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.imp_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.iff_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.ite_lid, threeTys))::((Microsoft_FStar_Absyn_Const.not_lid, oneType))::((Microsoft_FStar_Absyn_Const.eqT_lid, twoTypes))::((Microsoft_FStar_Absyn_Const.eq2_lid, twoTerms))::((Microsoft_FStar_Absyn_Const.eq2_lid, (Support.List.append twoTypes twoTerms)))::[]
in (let rec aux = (fun ( f ) ( _23_2286 ) -> (match (_23_2286) with
| (lid, arity) -> begin
(let _23_2289 = (head_and_args f)
in (match (_23_2289) with
| (t, args) -> begin
(match ((((is_constructor t lid) && ((Support.List.length args) = (Support.List.length arity))) && (Support.List.forall2 (fun ( arg ) ( flag ) -> (match (arg) with
| (Support.Microsoft.FStar.Util.Inl (_23_2293), _23_2296) -> begin
(flag = type_sort)
end
| (Support.Microsoft.FStar.Util.Inr (_23_2299), _23_2302) -> begin
(flag = term_sort)
end)) args arity))) with
| true -> begin
Some (BaseConn ((lid, args)))
end
| false -> begin
None
end)
end))
end))
in (Support.Microsoft.FStar.Util.find_map connectives (aux f))))))))
end)))
in (let patterns = (fun ( t ) -> (let t = (compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, pats))) -> begin
(let _68_10032 = (compress_typ t)
in (pats, _68_10032))
end
| _23_2313 -> begin
(let _68_10033 = (compress_typ t)
in ([], _68_10033))
end)))
in (let destruct_q_conn = (fun ( t ) -> (let is_q = (fun ( fa ) ( l ) -> (match (fa) with
| true -> begin
(is_forall l)
end
| false -> begin
(is_exists l)
end))
in (let flat = (fun ( t ) -> (let _23_2323 = (head_and_args t)
in (match (_23_2323) with
| (t, args) -> begin
(let _68_10047 = (Support.Prims.pipe_right args (Support.List.map (fun ( _23_26 ) -> (match (_23_26) with
| (Support.Microsoft.FStar.Util.Inl (t), imp) -> begin
(let _68_10044 = (let _68_10043 = (compress_typ t)
in Support.Microsoft.FStar.Util.Inl (_68_10043))
in (_68_10044, imp))
end
| (Support.Microsoft.FStar.Util.Inr (e), imp) -> begin
(let _68_10046 = (let _68_10045 = (compress_exp e)
in Support.Microsoft.FStar.Util.Inr (_68_10045))
in (_68_10046, imp))
end))))
in (t, _68_10047))
end)))
in (let rec aux = (fun ( qopt ) ( out ) ( t ) -> (match ((let _68_10054 = (flat t)
in (qopt, _68_10054))) with
| ((Some (fa), ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, (Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t2)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((Some (fa), ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _::(Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t2)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_q fa tc.Microsoft_FStar_Absyn_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, (Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t2)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((None, ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (tc); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _::(Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t2)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_qlid tc.Microsoft_FStar_Absyn_Syntax.v) -> begin
(aux (Some ((is_forall tc.Microsoft_FStar_Absyn_Syntax.v))) ((b)::out) t2)
end
| (Some (true), _23_2471) -> begin
(let _23_2475 = (patterns t)
in (match (_23_2475) with
| (pats, body) -> begin
Some (QAll (((Support.List.rev out), pats, body)))
end))
end
| (Some (false), _23_2479) -> begin
(let _23_2483 = (patterns t)
in (match (_23_2483) with
| (pats, body) -> begin
Some (QEx (((Support.List.rev out), pats, body)))
end))
end
| _23_2485 -> begin
None
end))
in (aux None [] t)))))
in (let phi = (compress_typ f)
in (match ((destruct_base_conn phi)) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end))))))




