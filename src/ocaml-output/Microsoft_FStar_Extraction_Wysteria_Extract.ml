
exception NYI of (string)

let is_NYI = (fun ( _discr_ ) -> (match (_discr_) with
| NYI (_) -> begin
true
end
| _ -> begin
false
end))

let is_valid_prims_ffi = (fun ( s ) -> (match (s) with
| ("op_Addition") | ("op_Subtraction") | ("op_Multiply") | ("op_Division") | ("op_Equality") | ("op_disEquality") | ("op_AmpAmp") | ("op_BarBar") | ("op_LessThanOrEqual") | ("op_GreaterThanOrEqual") | ("op_LessThan") | ("op_GreaterThan") | ("op_Modulus") -> begin
true
end
| _63_17 -> begin
false
end))

let is_ffi_fn = (fun ( e ) ( args_l ) -> (match ((let _71_25598 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _71_25598.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fvar, _63_22)) -> begin
(let fn_name = fvar.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText
in (let mlid = (Microsoft_FStar_Absyn_Syntax.lid_of_ids fvar.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ns)
in (match ((((Support.List.length mlid.Microsoft_FStar_Absyn_Syntax.ns) = 0) && (mlid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "OrdSet"))) with
| true -> begin
(let _71_25599 = (Support.List.tl args_l)
in (true, fn_name, _71_25599))
end
| false -> begin
(match ((((Support.List.length mlid.Microsoft_FStar_Absyn_Syntax.ns) = 0) && (mlid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText = "Prims"))) with
| true -> begin
((is_valid_prims_ffi fn_name), fn_name, args_l)
end
| false -> begin
(false, "", args_l)
end)
end)))
end
| _63_28 -> begin
(false, "", args_l)
end))

let process_wysteria_lib_fun_app_args = (fun ( s ) ( args ) -> (match (s) with
| ("unbox_p") | ("unbox_s") | ("mkwire_p") -> begin
(Support.List.tl args)
end
| _63_35 -> begin
args
end))

let extract_const = (fun ( c ) -> (match (c) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
"()"
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (b) -> begin
(match (b) with
| true -> begin
"true"
end
| false -> begin
"false"
end)
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (n) -> begin
(Support.Microsoft.FStar.Util.string_of_int32 n)
end
| Microsoft_FStar_Absyn_Syntax.Const_int (x) -> begin
x
end
| _63_45 -> begin
(raise (NYI ("Constant not expected")))
end))

let extract_binder = (fun ( b ) -> (match (b) with
| (Support.Microsoft.FStar.Util.Inl (_63_48), _63_51) -> begin
""
end
| (Support.Microsoft.FStar.Util.Inr (bvar), _63_56) -> begin
bvar.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText
end))

let rec extract_exp = (fun ( e ) -> (match ((let _71_25613 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _71_25613.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (bvar) -> begin
bvar.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fvar, _63_63)) -> begin
fvar.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(extract_const c)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, e)) -> begin
(let bs_str = (Support.List.fold_left (fun ( s ) ( b ) -> (Support.String.strcat (Support.String.strcat (Support.String.strcat s "fun ") (extract_binder b)) ". ")) "" bs)
in (let s' = (extract_exp e)
in (Support.String.strcat bs_str s')))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((e, args)) -> begin
(let args = (Support.List.filter (fun ( a ) -> (match (a) with
| (Support.Microsoft.FStar.Util.Inl (_63_82), _63_85) -> begin
false
end
| (Support.Microsoft.FStar.Util.Inr (_63_88), _63_91) -> begin
true
end)) args)
in (let _63_97 = (is_ffi_fn e args)
in (match (_63_97) with
| (b, fn, args) -> begin
(match (b) with
| true -> begin
(let args_s = (Support.List.fold_left (fun ( s ) ( a ) -> (let _71_25620 = (let _71_25619 = (extract_arg a)
in (Support.String.strcat s _71_25619))
in (Support.String.strcat _71_25620 "; "))) "" args)
in (Support.String.strcat (Support.String.strcat (Support.String.strcat (Support.String.strcat "sysop \"" fn) "\" [ ") args_s) " ]"))
end
| false -> begin
(let s = (extract_exp e)
in (let args = (process_wysteria_lib_fun_app_args s args)
in (Support.List.fold_left (fun ( s ) ( a ) -> (let _71_25624 = (let _71_25623 = (extract_arg a)
in (Support.String.strcat s _71_25623))
in (Support.String.strcat _71_25624 " "))) (Support.String.strcat s " ") args)))
end)
end)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(let s = (extract_exp e)
in (let _71_25625 = (extract_pats pats)
in (Support.String.strcat (Support.String.strcat s "\n") _71_25625)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, _63_112, _63_114)) -> begin
(extract_exp e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, e)) -> begin
(match ((Support.Prims.fst lbs)) with
| true -> begin
(raise (NYI ("Recursive let not expected")))
end
| false -> begin
(let lb = (Support.List.hd (Support.Prims.snd lbs))
in (let _71_25632 = (let _71_25630 = (let _71_25629 = (let _71_25627 = (let _71_25626 = (Microsoft_FStar_Absyn_Print.lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (Support.String.strcat "let " _71_25626))
in (Support.String.strcat _71_25627 " = "))
in (let _71_25628 = (extract_exp lb.Microsoft_FStar_Absyn_Syntax.lbdef)
in (Support.String.strcat _71_25629 _71_25628)))
in (Support.String.strcat _71_25630 " in\n"))
in (let _71_25631 = (extract_exp e)
in (Support.String.strcat _71_25632 _71_25631))))
end)
end
| (Microsoft_FStar_Absyn_Syntax.Exp_uvar (_)) | (_) -> begin
(let _63_127 = (let _71_25634 = (let _71_25633 = (Microsoft_FStar_Absyn_Print.tag_of_exp e)
in (Support.String.strcat "Expression not expected " _71_25633))
in (Support.Microsoft.FStar.Util.print_string _71_25634))
in (raise (NYI (""))))
end))
and extract_arg = (fun ( a ) -> (match (a) with
| (Support.Microsoft.FStar.Util.Inl (_63_131), _63_134) -> begin
(raise (NYI ("This should not have happened")))
end
| (Support.Microsoft.FStar.Util.Inr (e), _63_139) -> begin
(let _71_25637 = (let _71_25636 = (extract_exp e)
in (Support.String.strcat "( " _71_25636))
in (Support.String.strcat _71_25637 " )"))
end))
and extract_pats = (fun ( pats ) -> (Support.List.fold_left (fun ( s ) ( _63_146 ) -> (match (_63_146) with
| (p, w, e) -> begin
(let s' = (let _71_25644 = (let _71_25642 = (let _71_25641 = (extract_pat p)
in (Support.String.strcat "| " _71_25641))
in (Support.String.strcat _71_25642 " -> "))
in (let _71_25643 = (extract_exp e)
in (Support.String.strcat _71_25644 _71_25643)))
in (Support.String.strcat (Support.String.strcat s "\n") s))
end)) "" pats))
and extract_pat = (fun ( p ) -> (match (p.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(extract_const c)
end
| _63_152 -> begin
(raise (NYI ("Pattern not expected")))
end))

let extract_sigelt = (fun ( s ) -> (match (s) with
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, _63_156, _63_158, _63_160)) -> begin
(match ((Support.Prims.fst lbs)) with
| true -> begin
(raise (NYI ("Recursive let not expected")))
end
| false -> begin
(let lb = (Support.List.hd (Support.Prims.snd lbs))
in (let _71_25652 = (let _71_25651 = (let _71_25649 = (let _71_25648 = (Microsoft_FStar_Absyn_Print.lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (Support.String.strcat "let " _71_25648))
in (Support.String.strcat _71_25649 " = "))
in (let _71_25650 = (extract_exp lb.Microsoft_FStar_Absyn_Syntax.lbdef)
in (Support.String.strcat _71_25651 _71_25650)))
in (Support.String.strcat _71_25652 " in")))
end)
end
| _63_165 -> begin
""
end))

let extract = (fun ( m ) -> (let name = m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str
in (let _63_168 = (Support.Microsoft.FStar.Util.print_string (Support.String.strcat (Support.String.strcat "Extracting module: " name) "\n"))
in (match ((name = "Examples")) with
| true -> begin
(let s = (Support.List.fold_left (fun ( s ) ( sigelt ) -> (let _71_25657 = (extract_sigelt sigelt)
in (Support.String.strcat (Support.String.strcat s "\n") _71_25657))) "" m.Microsoft_FStar_Absyn_Syntax.declarations)
in (Support.Microsoft.FStar.Util.print_string (Support.String.strcat s "\n")))
end
| false -> begin
()
end))))




