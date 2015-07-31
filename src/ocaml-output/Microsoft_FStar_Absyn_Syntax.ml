
exception Err of (string)

let is_Err = (fun ( _discr_ ) -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))

exception Error of ((string * Support.Microsoft.FStar.Range.range))

let is_Error = (fun ( _discr_ ) -> (match (_discr_) with
| Error (_) -> begin
true
end
| _ -> begin
false
end))

exception Warning of ((string * Support.Microsoft.FStar.Range.range))

let is_Warning = (fun ( _discr_ ) -> (match (_discr_) with
| Warning (_) -> begin
true
end
| _ -> begin
false
end))

type ident =
{idText : string; idRange : Support.Microsoft.FStar.Range.range}

let is_Mkident = (fun ( _ ) -> (failwith ("Not yet implemented")))

type l__LongIdent =
{ns : ident list; ident : ident; nsstr : string; str : string}

let is_MkLongIdent = (fun ( _ ) -> (failwith ("Not yet implemented")))

type lident =
l__LongIdent

type ('a, 't) withinfo_t =
{v : 'a; sort : 't; p : Support.Microsoft.FStar.Range.range}

let is_Mkwithinfo_t = (fun ( _ ) -> (failwith ("Not yet implemented")))

type 't var =
(lident, 't) withinfo_t

type fieldname =
lident

type 'a bvdef =
{ppname : ident; realname : ident}

let is_Mkbvdef = (fun ( _ ) -> (failwith ("Not yet implemented")))

type ('a, 't) bvar =
('a bvdef, 't) withinfo_t

type sconst =
| Const_unit
| Const_uint8 of Support.Prims.byte
| Const_bool of bool
| Const_int32 of Support.Prims.int32
| Const_int64 of Int64.t
| Const_int of string
| Const_char of char
| Const_float of Support.Prims.double
| Const_bytearray of (Support.Prims.byte array * Support.Microsoft.FStar.Range.range)
| Const_string of (Support.Prims.byte array * Support.Microsoft.FStar.Range.range)

let is_Const_unit = (fun ( _discr_ ) -> (match (_discr_) with
| Const_unit -> begin
true
end
| _ -> begin
false
end))

let is_Const_uint8 = (fun ( _discr_ ) -> (match (_discr_) with
| Const_uint8 (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_bool = (fun ( _discr_ ) -> (match (_discr_) with
| Const_bool (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_int32 = (fun ( _discr_ ) -> (match (_discr_) with
| Const_int32 (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_int64 = (fun ( _discr_ ) -> (match (_discr_) with
| Const_int64 (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_int = (fun ( _discr_ ) -> (match (_discr_) with
| Const_int (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_char = (fun ( _discr_ ) -> (match (_discr_) with
| Const_char (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_float = (fun ( _discr_ ) -> (match (_discr_) with
| Const_float (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_bytearray = (fun ( _discr_ ) -> (match (_discr_) with
| Const_bytearray (_) -> begin
true
end
| _ -> begin
false
end))

let is_Const_string = (fun ( _discr_ ) -> (match (_discr_) with
| Const_string (_) -> begin
true
end
| _ -> begin
false
end))

type pragma =
| SetOptions of string
| ResetOptions

let is_SetOptions = (fun ( _discr_ ) -> (match (_discr_) with
| SetOptions (_) -> begin
true
end
| _ -> begin
false
end))

let is_ResetOptions = (fun ( _discr_ ) -> (match (_discr_) with
| ResetOptions -> begin
true
end
| _ -> begin
false
end))

type 'a memo =
'a option ref

type arg_qualifier =
| Implicit
| Equality

let is_Implicit = (fun ( _discr_ ) -> (match (_discr_) with
| Implicit -> begin
true
end
| _ -> begin
false
end))

let is_Equality = (fun ( _discr_ ) -> (match (_discr_) with
| Equality -> begin
true
end
| _ -> begin
false
end))

type aqual =
arg_qualifier option

type typ' =
| Typ_btvar of btvar
| Typ_const of ftvar
| Typ_fun of (binders * comp)
| Typ_refine of (bvvar * typ)
| Typ_app of (typ * args)
| Typ_lam of (binders * typ)
| Typ_ascribed of (typ * knd)
| Typ_meta of meta_t
| Typ_uvar of (uvar_t * knd)
| Typ_delayed of (((typ * subst_t), unit  ->  typ) Support.Microsoft.FStar.Util.either * typ memo)
| Typ_unknown 
 and comp_typ =
{effect_name : lident; result_typ : typ; effect_args : args; flags : cflags list} 
 and comp' =
| Total of typ
| Comp of comp_typ 
 and cflags =
| TOTAL
| MLEFFECT
| RETURN
| PARTIAL_RETURN
| SOMETRIVIAL
| LEMMA
| DECREASES of exp 
 and meta_t =
| Meta_pattern of (typ * arg list)
| Meta_named of (typ * lident)
| Meta_labeled of (typ * string * Support.Microsoft.FStar.Range.range * bool)
| Meta_refresh_label of (typ * bool option * Support.Microsoft.FStar.Range.range)
| Meta_slack_formula of (typ * typ * bool ref) 
 and 'a uvar_basis =
| Uvar
| Fixed of 'a 
 and exp' =
| Exp_bvar of bvvar
| Exp_fvar of (fvvar * fv_qual option)
| Exp_constant of sconst
| Exp_abs of (binders * exp)
| Exp_app of (exp * args)
| Exp_match of (exp * (pat * exp option * exp) list)
| Exp_ascribed of (exp * typ * lident option)
| Exp_let of (letbindings * exp)
| Exp_uvar of (uvar_e * typ)
| Exp_delayed of (exp * subst_t * exp memo)
| Exp_meta of meta_e 
 and meta_e =
| Meta_desugared of (exp * meta_source_info) 
 and meta_source_info =
| Data_app
| Sequence
| Primop
| MaskedEffect 
 and fv_qual =
| Data_ctor
| Record_projector of lident
| Record_ctor of (lident * fieldname list) 
 and pat' =
| Pat_disj of pat list
| Pat_constant of sconst
| Pat_cons of (fvvar * fv_qual option * pat list)
| Pat_var of (bvvar * bool)
| Pat_tvar of btvar
| Pat_wild of bvvar
| Pat_twild of btvar
| Pat_dot_term of (bvvar * exp)
| Pat_dot_typ of (btvar * typ) 
 and knd' =
| Kind_type
| Kind_effect
| Kind_abbrev of (kabbrev * knd)
| Kind_arrow of (binders * knd)
| Kind_uvar of uvar_k_app
| Kind_lam of (binders * knd)
| Kind_delayed of (knd * subst_t * knd memo)
| Kind_unknown 
 and letbinding =
{lbname : lbname; lbtyp : typ; lbeff : lident; lbdef : exp} 
 and freevars =
{ftvs : btvar Support.Microsoft.FStar.Util.set; fxvs : bvvar Support.Microsoft.FStar.Util.set} 
 and uvars =
{uvars_k : uvar_k Support.Microsoft.FStar.Util.set; uvars_t : (uvar_t * knd) Support.Microsoft.FStar.Util.set; uvars_e : (uvar_e * typ) Support.Microsoft.FStar.Util.set} 
 and ('a, 'b) syntax =
{n : 'a; tk : 'b memo; pos : Support.Microsoft.FStar.Range.range; fvs : freevars memo; uvs : uvars memo} 
 and arg =
((typ, exp) Support.Microsoft.FStar.Util.either * aqual) 
 and args =
arg list 
 and binder =
((btvar, bvvar) Support.Microsoft.FStar.Util.either * arg_qualifier option) 
 and binders =
binder list 
 and typ =
(typ', knd) syntax 
 and comp =
(comp', unit) syntax 
 and uvar_t =
typ uvar_basis Support.Microsoft.FStar.Unionfind.uvar 
 and exp =
(exp', typ) syntax 
 and uvar_e =
exp uvar_basis Support.Microsoft.FStar.Unionfind.uvar 
 and btvdef =
typ bvdef 
 and bvvdef =
exp bvdef 
 and pat =
(pat', (knd, typ) Support.Microsoft.FStar.Util.either option) withinfo_t 
 and knd =
(knd', unit) syntax 
 and uvar_k_app =
(uvar_k * args) 
 and kabbrev =
(lident * args) 
 and uvar_k =
knd uvar_basis Support.Microsoft.FStar.Unionfind.uvar 
 and lbname =
(bvvdef, lident) Support.Microsoft.FStar.Util.either 
 and letbindings =
(bool * letbinding list) 
 and subst_t =
subst_elt list list 
 and subst_map =
(typ, exp) Support.Microsoft.FStar.Util.either Support.Microsoft.FStar.Util.smap 
 and subst_elt =
((btvdef * typ), (bvvdef * exp)) Support.Microsoft.FStar.Util.either 
 and fvar =
(btvdef, bvvdef) Support.Microsoft.FStar.Util.either 
 and btvar =
(typ, knd) bvar 
 and bvvar =
(exp, typ) bvar 
 and ftvar =
knd var 
 and fvvar =
typ var

let is_Typ_btvar = (fun ( _discr_ ) -> (match (_discr_) with
| Typ_btvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_const = (fun ( _discr_ ) -> (match (_discr_) with
| Typ_const (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_fun = (fun ( _discr_ ) -> (match (_discr_) with
| Typ_fun (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_refine = (fun ( _discr_ ) -> (match (_discr_) with
| Typ_refine (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_app = (fun ( _discr_ ) -> (match (_discr_) with
| Typ_app (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_lam = (fun ( _discr_ ) -> (match (_discr_) with
| Typ_lam (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_ascribed = (fun ( _discr_ ) -> (match (_discr_) with
| Typ_ascribed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_meta = (fun ( _discr_ ) -> (match (_discr_) with
| Typ_meta (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_uvar = (fun ( _discr_ ) -> (match (_discr_) with
| Typ_uvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_delayed = (fun ( _discr_ ) -> (match (_discr_) with
| Typ_delayed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Typ_unknown = (fun ( _discr_ ) -> (match (_discr_) with
| Typ_unknown -> begin
true
end
| _ -> begin
false
end))

let is_Mkcomp_typ = (fun ( _ ) -> (failwith ("Not yet implemented")))

let is_Total = (fun ( _discr_ ) -> (match (_discr_) with
| Total (_) -> begin
true
end
| _ -> begin
false
end))

let is_Comp = (fun ( _discr_ ) -> (match (_discr_) with
| Comp (_) -> begin
true
end
| _ -> begin
false
end))

let is_TOTAL = (fun ( _discr_ ) -> (match (_discr_) with
| TOTAL -> begin
true
end
| _ -> begin
false
end))

let is_MLEFFECT = (fun ( _discr_ ) -> (match (_discr_) with
| MLEFFECT -> begin
true
end
| _ -> begin
false
end))

let is_RETURN = (fun ( _discr_ ) -> (match (_discr_) with
| RETURN -> begin
true
end
| _ -> begin
false
end))

let is_PARTIAL_RETURN = (fun ( _discr_ ) -> (match (_discr_) with
| PARTIAL_RETURN -> begin
true
end
| _ -> begin
false
end))

let is_SOMETRIVIAL = (fun ( _discr_ ) -> (match (_discr_) with
| SOMETRIVIAL -> begin
true
end
| _ -> begin
false
end))

let is_LEMMA = (fun ( _discr_ ) -> (match (_discr_) with
| LEMMA -> begin
true
end
| _ -> begin
false
end))

let is_DECREASES = (fun ( _discr_ ) -> (match (_discr_) with
| DECREASES (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_pattern = (fun ( _discr_ ) -> (match (_discr_) with
| Meta_pattern (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_named = (fun ( _discr_ ) -> (match (_discr_) with
| Meta_named (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_labeled = (fun ( _discr_ ) -> (match (_discr_) with
| Meta_labeled (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_refresh_label = (fun ( _discr_ ) -> (match (_discr_) with
| Meta_refresh_label (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_slack_formula = (fun ( _discr_ ) -> (match (_discr_) with
| Meta_slack_formula (_) -> begin
true
end
| _ -> begin
false
end))

let is_Uvar = (fun ( _discr_ ) -> (match (_discr_) with
| Uvar -> begin
true
end
| _ -> begin
false
end))

let is_Fixed = (fun ( _discr_ ) -> (match (_discr_) with
| Fixed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_bvar = (fun ( _discr_ ) -> (match (_discr_) with
| Exp_bvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_fvar = (fun ( _discr_ ) -> (match (_discr_) with
| Exp_fvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_constant = (fun ( _discr_ ) -> (match (_discr_) with
| Exp_constant (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_abs = (fun ( _discr_ ) -> (match (_discr_) with
| Exp_abs (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_app = (fun ( _discr_ ) -> (match (_discr_) with
| Exp_app (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_match = (fun ( _discr_ ) -> (match (_discr_) with
| Exp_match (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_ascribed = (fun ( _discr_ ) -> (match (_discr_) with
| Exp_ascribed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_let = (fun ( _discr_ ) -> (match (_discr_) with
| Exp_let (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_uvar = (fun ( _discr_ ) -> (match (_discr_) with
| Exp_uvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_delayed = (fun ( _discr_ ) -> (match (_discr_) with
| Exp_delayed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exp_meta = (fun ( _discr_ ) -> (match (_discr_) with
| Exp_meta (_) -> begin
true
end
| _ -> begin
false
end))

let is_Meta_desugared = (fun ( _discr_ ) -> (match (_discr_) with
| Meta_desugared (_) -> begin
true
end
| _ -> begin
false
end))

let is_Data_app = (fun ( _discr_ ) -> (match (_discr_) with
| Data_app -> begin
true
end
| _ -> begin
false
end))

let is_Sequence = (fun ( _discr_ ) -> (match (_discr_) with
| Sequence -> begin
true
end
| _ -> begin
false
end))

let is_Primop = (fun ( _discr_ ) -> (match (_discr_) with
| Primop -> begin
true
end
| _ -> begin
false
end))

let is_MaskedEffect = (fun ( _discr_ ) -> (match (_discr_) with
| MaskedEffect -> begin
true
end
| _ -> begin
false
end))

let is_Data_ctor = (fun ( _discr_ ) -> (match (_discr_) with
| Data_ctor -> begin
true
end
| _ -> begin
false
end))

let is_Record_projector = (fun ( _discr_ ) -> (match (_discr_) with
| Record_projector (_) -> begin
true
end
| _ -> begin
false
end))

let is_Record_ctor = (fun ( _discr_ ) -> (match (_discr_) with
| Record_ctor (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_disj = (fun ( _discr_ ) -> (match (_discr_) with
| Pat_disj (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_constant = (fun ( _discr_ ) -> (match (_discr_) with
| Pat_constant (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_cons = (fun ( _discr_ ) -> (match (_discr_) with
| Pat_cons (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_var = (fun ( _discr_ ) -> (match (_discr_) with
| Pat_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_tvar = (fun ( _discr_ ) -> (match (_discr_) with
| Pat_tvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_wild = (fun ( _discr_ ) -> (match (_discr_) with
| Pat_wild (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_twild = (fun ( _discr_ ) -> (match (_discr_) with
| Pat_twild (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_dot_term = (fun ( _discr_ ) -> (match (_discr_) with
| Pat_dot_term (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pat_dot_typ = (fun ( _discr_ ) -> (match (_discr_) with
| Pat_dot_typ (_) -> begin
true
end
| _ -> begin
false
end))

let is_Kind_type = (fun ( _discr_ ) -> (match (_discr_) with
| Kind_type -> begin
true
end
| _ -> begin
false
end))

let is_Kind_effect = (fun ( _discr_ ) -> (match (_discr_) with
| Kind_effect -> begin
true
end
| _ -> begin
false
end))

let is_Kind_abbrev = (fun ( _discr_ ) -> (match (_discr_) with
| Kind_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_Kind_arrow = (fun ( _discr_ ) -> (match (_discr_) with
| Kind_arrow (_) -> begin
true
end
| _ -> begin
false
end))

let is_Kind_uvar = (fun ( _discr_ ) -> (match (_discr_) with
| Kind_uvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Kind_lam = (fun ( _discr_ ) -> (match (_discr_) with
| Kind_lam (_) -> begin
true
end
| _ -> begin
false
end))

let is_Kind_delayed = (fun ( _discr_ ) -> (match (_discr_) with
| Kind_delayed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Kind_unknown = (fun ( _discr_ ) -> (match (_discr_) with
| Kind_unknown -> begin
true
end
| _ -> begin
false
end))

let is_Mkletbinding = (fun ( _ ) -> (failwith ("Not yet implemented")))

let is_Mkfreevars = (fun ( _ ) -> (failwith ("Not yet implemented")))

let is_Mkuvars = (fun ( _ ) -> (failwith ("Not yet implemented")))

let is_Mksyntax = (fun ( _ ) -> (failwith ("Not yet implemented")))

type subst =
subst_elt list

type either_var =
(btvar, bvvar) Support.Microsoft.FStar.Util.either

type freevars_l =
either_var list

type formula =
typ

type formulae =
typ list

type qualifier =
| Private
| Assumption
| Opaque
| Logic
| Discriminator of lident
| Projector of (lident * (btvdef, bvvdef) Support.Microsoft.FStar.Util.either)
| RecordType of fieldname list
| RecordConstructor of fieldname list
| ExceptionConstructor
| DefaultEffect of lident option
| TotalEffect
| HasMaskedEffect
| Effect

let is_Private = (fun ( _discr_ ) -> (match (_discr_) with
| Private -> begin
true
end
| _ -> begin
false
end))

let is_Assumption = (fun ( _discr_ ) -> (match (_discr_) with
| Assumption -> begin
true
end
| _ -> begin
false
end))

let is_Opaque = (fun ( _discr_ ) -> (match (_discr_) with
| Opaque -> begin
true
end
| _ -> begin
false
end))

let is_Logic = (fun ( _discr_ ) -> (match (_discr_) with
| Logic -> begin
true
end
| _ -> begin
false
end))

let is_Discriminator = (fun ( _discr_ ) -> (match (_discr_) with
| Discriminator (_) -> begin
true
end
| _ -> begin
false
end))

let is_Projector = (fun ( _discr_ ) -> (match (_discr_) with
| Projector (_) -> begin
true
end
| _ -> begin
false
end))

let is_RecordType = (fun ( _discr_ ) -> (match (_discr_) with
| RecordType (_) -> begin
true
end
| _ -> begin
false
end))

let is_RecordConstructor = (fun ( _discr_ ) -> (match (_discr_) with
| RecordConstructor (_) -> begin
true
end
| _ -> begin
false
end))

let is_ExceptionConstructor = (fun ( _discr_ ) -> (match (_discr_) with
| ExceptionConstructor -> begin
true
end
| _ -> begin
false
end))

let is_DefaultEffect = (fun ( _discr_ ) -> (match (_discr_) with
| DefaultEffect (_) -> begin
true
end
| _ -> begin
false
end))

let is_TotalEffect = (fun ( _discr_ ) -> (match (_discr_) with
| TotalEffect -> begin
true
end
| _ -> begin
false
end))

let is_HasMaskedEffect = (fun ( _discr_ ) -> (match (_discr_) with
| HasMaskedEffect -> begin
true
end
| _ -> begin
false
end))

let is_Effect = (fun ( _discr_ ) -> (match (_discr_) with
| Effect -> begin
true
end
| _ -> begin
false
end))

type tycon =
(lident * binders * knd)

type monad_abbrev =
{mabbrev : lident; parms : binders; def : typ}

let is_Mkmonad_abbrev = (fun ( _ ) -> (failwith ("Not yet implemented")))

type sub_eff =
{source : lident; target : lident; lift : typ}

let is_Mksub_eff = (fun ( _ ) -> (failwith ("Not yet implemented")))

type eff_decl =
{mname : lident; binders : binders; qualifiers : qualifier list; signature : knd; ret : typ; bind_wp : typ; bind_wlp : typ; if_then_else : typ; ite_wp : typ; ite_wlp : typ; wp_binop : typ; wp_as_type : typ; close_wp : typ; close_wp_t : typ; assert_p : typ; assume_p : typ; null_wp : typ; trivial : typ} 
 and sigelt =
| Sig_tycon of (lident * binders * knd * lident list * lident list * qualifier list * Support.Microsoft.FStar.Range.range)
| Sig_kind_abbrev of (lident * binders * knd * Support.Microsoft.FStar.Range.range)
| Sig_typ_abbrev of (lident * binders * knd * typ * qualifier list * Support.Microsoft.FStar.Range.range)
| Sig_datacon of (lident * typ * tycon * qualifier list * lident list * Support.Microsoft.FStar.Range.range)
| Sig_val_decl of (lident * typ * qualifier list * Support.Microsoft.FStar.Range.range)
| Sig_assume of (lident * formula * qualifier list * Support.Microsoft.FStar.Range.range)
| Sig_let of (letbindings * Support.Microsoft.FStar.Range.range * lident list * qualifier list)
| Sig_main of (exp * Support.Microsoft.FStar.Range.range)
| Sig_bundle of (sigelt list * qualifier list * lident list * Support.Microsoft.FStar.Range.range)
| Sig_new_effect of (eff_decl * Support.Microsoft.FStar.Range.range)
| Sig_sub_effect of (sub_eff * Support.Microsoft.FStar.Range.range)
| Sig_effect_abbrev of (lident * binders * comp * qualifier list * Support.Microsoft.FStar.Range.range)
| Sig_pragma of (pragma * Support.Microsoft.FStar.Range.range)

let is_Mkeff_decl = (fun ( _ ) -> (failwith ("Not yet implemented")))

let is_Sig_tycon = (fun ( _discr_ ) -> (match (_discr_) with
| Sig_tycon (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_kind_abbrev = (fun ( _discr_ ) -> (match (_discr_) with
| Sig_kind_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_typ_abbrev = (fun ( _discr_ ) -> (match (_discr_) with
| Sig_typ_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_datacon = (fun ( _discr_ ) -> (match (_discr_) with
| Sig_datacon (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_val_decl = (fun ( _discr_ ) -> (match (_discr_) with
| Sig_val_decl (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_assume = (fun ( _discr_ ) -> (match (_discr_) with
| Sig_assume (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_let = (fun ( _discr_ ) -> (match (_discr_) with
| Sig_let (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_main = (fun ( _discr_ ) -> (match (_discr_) with
| Sig_main (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_bundle = (fun ( _discr_ ) -> (match (_discr_) with
| Sig_bundle (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_new_effect = (fun ( _discr_ ) -> (match (_discr_) with
| Sig_new_effect (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_sub_effect = (fun ( _discr_ ) -> (match (_discr_) with
| Sig_sub_effect (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_effect_abbrev = (fun ( _discr_ ) -> (match (_discr_) with
| Sig_effect_abbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sig_pragma = (fun ( _discr_ ) -> (match (_discr_) with
| Sig_pragma (_) -> begin
true
end
| _ -> begin
false
end))

type sigelts =
sigelt list

type modul =
{name : lident; declarations : sigelts; exports : sigelts; is_interface : bool; is_deserialized : bool}

let is_Mkmodul = (fun ( _ ) -> (failwith ("Not yet implemented")))

type ktec =
| K of knd
| T of (typ * knd option)
| E of exp
| C of comp

let is_K = (fun ( _discr_ ) -> (match (_discr_) with
| K (_) -> begin
true
end
| _ -> begin
false
end))

let is_T = (fun ( _discr_ ) -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

let is_E = (fun ( _discr_ ) -> (match (_discr_) with
| E (_) -> begin
true
end
| _ -> begin
false
end))

let is_C = (fun ( _discr_ ) -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))

type lcomp =
{eff_name : lident; res_typ : typ; cflags : cflags list; comp : unit  ->  comp}

let is_Mklcomp = (fun ( _ ) -> (failwith ("Not yet implemented")))

type path =
string list

let dummyRange = 0L

let withinfo = (fun ( v ) ( s ) ( r ) -> {v = v; sort = s; p = r})

let withsort = (fun ( v ) ( s ) -> (withinfo v s dummyRange))

let mk_ident = (fun ( _20_261 ) -> (match (_20_261) with
| (text, range) -> begin
{idText = text; idRange = range}
end))

let id_of_text = (fun ( str ) -> (mk_ident (str, dummyRange)))

let text_of_id = (fun ( id ) -> id.idText)

let text_of_path = (fun ( path ) -> (Support.Microsoft.FStar.Util.concat_l "." path))

let path_of_text = (fun ( text ) -> (Support.String.split (('.')::[]) text))

let path_of_ns = (fun ( ns ) -> (Support.List.map text_of_id ns))

let path_of_lid = (fun ( lid ) -> (Support.List.map text_of_id (Support.List.append lid.ns ((lid.ident)::[]))))

let ids_of_lid = (fun ( lid ) -> (Support.List.append lid.ns ((lid.ident)::[])))

let lid_of_ids = (fun ( ids ) -> (let _20_272 = (Support.Microsoft.FStar.Util.prefix ids)
in (match (_20_272) with
| (ns, id) -> begin
(let nsstr = (let _68_7307 = (Support.List.map text_of_id ns)
in (Support.Prims.pipe_right _68_7307 text_of_path))
in {ns = ns; ident = id; nsstr = nsstr; str = (match ((nsstr = "")) with
| true -> begin
id.idText
end
| false -> begin
(Support.String.strcat (Support.String.strcat nsstr ".") id.idText)
end)})
end)))

let lid_of_path = (fun ( path ) ( pos ) -> (let ids = (Support.List.map (fun ( s ) -> (mk_ident (s, pos))) path)
in (lid_of_ids ids)))

let text_of_lid = (fun ( lid ) -> lid.str)

let lid_equals = (fun ( l1 ) ( l2 ) -> (l1.str = l2.str))

let bvd_eq = (fun ( bvd1 ) ( bvd2 ) -> (bvd1.realname.idText = bvd2.realname.idText))

let order_bvd = (fun ( x ) ( y ) -> (match ((x, y)) with
| (Support.Microsoft.FStar.Util.Inl (_), Support.Microsoft.FStar.Util.Inr (_)) -> begin
(- (1))
end
| (Support.Microsoft.FStar.Util.Inr (_), Support.Microsoft.FStar.Util.Inl (_)) -> begin
1
end
| (Support.Microsoft.FStar.Util.Inl (x), Support.Microsoft.FStar.Util.Inl (y)) -> begin
(Support.String.compare x.realname.idText y.realname.idText)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Support.String.compare x.realname.idText y.realname.idText)
end))

let lid_with_range = (fun ( lid ) ( r ) -> (let id = (let _20_312 = lid.ident
in {idText = _20_312.idText; idRange = r})
in (let _20_315 = lid
in {ns = _20_315.ns; ident = id; nsstr = _20_315.nsstr; str = _20_315.str})))

let range_of_lid = (fun ( lid ) -> lid.ident.idRange)

let range_of_lbname = (fun ( l ) -> (match (l) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
x.ppname.idRange
end
| Support.Microsoft.FStar.Util.Inr (l) -> begin
(range_of_lid l)
end))

let syn = (fun ( p ) ( k ) ( f ) -> (f k p))

let mk_fvs = (fun ( _20_326 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.mk_ref None)
end))

let mk_uvs = (fun ( _20_327 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.mk_ref None)
end))

let new_ftv_set = (fun ( _20_328 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.new_set (fun ( x ) ( y ) -> (Support.Microsoft.FStar.Util.compare x.v.realname.idText y.v.realname.idText)) (fun ( x ) -> (Support.Microsoft.FStar.Util.hashcode x.v.realname.idText)))
end))

let new_uv_set = (fun ( _20_332 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.new_set (fun ( x ) ( y ) -> ((Support.Microsoft.FStar.Unionfind.uvar_id x) - (Support.Microsoft.FStar.Unionfind.uvar_id y))) Support.Microsoft.FStar.Unionfind.uvar_id)
end))

let new_uvt_set = (fun ( _20_335 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.new_set (fun ( _20_343 ) ( _20_347 ) -> (match ((_20_343, _20_347)) with
| ((x, _), (y, _)) -> begin
((Support.Microsoft.FStar.Unionfind.uvar_id x) - (Support.Microsoft.FStar.Unionfind.uvar_id y))
end)) (fun ( _20_339 ) -> (match (_20_339) with
| (x, _) -> begin
(Support.Microsoft.FStar.Unionfind.uvar_id x)
end)))
end))

let no_fvs = (let _68_7356 = (new_ftv_set ())
in (let _68_7355 = (new_ftv_set ())
in {ftvs = _68_7356; fxvs = _68_7355}))

let no_uvs = (let _68_7359 = (new_uv_set ())
in (let _68_7358 = (new_uvt_set ())
in (let _68_7357 = (new_uvt_set ())
in {uvars_k = _68_7359; uvars_t = _68_7358; uvars_e = _68_7357})))

let memo_no_uvs = (Support.Microsoft.FStar.Util.mk_ref (Some (no_uvs)))

let memo_no_fvs = (Support.Microsoft.FStar.Util.mk_ref (Some (no_fvs)))

let freevars_of_list = (fun ( l ) -> (Support.Prims.pipe_right l (Support.List.fold_left (fun ( out ) ( _20_1 ) -> (match (_20_1) with
| Support.Microsoft.FStar.Util.Inl (btv) -> begin
(let _20_353 = out
in (let _68_7364 = (Support.Microsoft.FStar.Util.set_add btv out.ftvs)
in {ftvs = _68_7364; fxvs = _20_353.fxvs}))
end
| Support.Microsoft.FStar.Util.Inr (bxv) -> begin
(let _20_357 = out
in (let _68_7365 = (Support.Microsoft.FStar.Util.set_add bxv out.fxvs)
in {ftvs = _20_357.ftvs; fxvs = _68_7365}))
end)) no_fvs)))

let list_of_freevars = (fun ( fvs ) -> (let _68_7373 = (let _68_7369 = (Support.Microsoft.FStar.Util.set_elements fvs.ftvs)
in (Support.Prims.pipe_right _68_7369 (Support.List.map (fun ( x ) -> Support.Microsoft.FStar.Util.Inl (x)))))
in (let _68_7372 = (let _68_7371 = (Support.Microsoft.FStar.Util.set_elements fvs.fxvs)
in (Support.Prims.pipe_right _68_7371 (Support.List.map (fun ( x ) -> Support.Microsoft.FStar.Util.Inr (x)))))
in (Support.List.append _68_7373 _68_7372))))

let get_unit_ref = (fun ( _20_362 ) -> (match (()) with
| () -> begin
(let x = (Support.Microsoft.FStar.Util.mk_ref (Some (())))
in (let _20_364 = (Support.ST.op_Colon_Equals x None)
in x))
end))

let mk_Kind_type = (let _68_7378 = (get_unit_ref ())
in (let _68_7377 = (mk_fvs ())
in (let _68_7376 = (mk_uvs ())
in {n = Kind_type; tk = _68_7378; pos = dummyRange; fvs = _68_7377; uvs = _68_7376})))

let mk_Kind_effect = (let _68_7381 = (get_unit_ref ())
in (let _68_7380 = (mk_fvs ())
in (let _68_7379 = (mk_uvs ())
in {n = Kind_effect; tk = _68_7381; pos = dummyRange; fvs = _68_7380; uvs = _68_7379})))

let mk_Kind_abbrev = (fun ( _20_368 ) ( p ) -> (match (_20_368) with
| (kabr, k) -> begin
(let _68_7388 = (get_unit_ref ())
in (let _68_7387 = (mk_fvs ())
in (let _68_7386 = (mk_uvs ())
in {n = Kind_abbrev ((kabr, k)); tk = _68_7388; pos = p; fvs = _68_7387; uvs = _68_7386})))
end))

let mk_Kind_arrow = (fun ( _20_372 ) ( p ) -> (match (_20_372) with
| (bs, k) -> begin
(let _68_7395 = (get_unit_ref ())
in (let _68_7394 = (mk_fvs ())
in (let _68_7393 = (mk_uvs ())
in {n = Kind_arrow ((bs, k)); tk = _68_7395; pos = p; fvs = _68_7394; uvs = _68_7393})))
end))

let mk_Kind_arrow' = (fun ( _20_376 ) ( p ) -> (match (_20_376) with
| (bs, k) -> begin
(match (bs) with
| [] -> begin
k
end
| _ -> begin
(match (k.n) with
| Kind_arrow ((bs', k')) -> begin
(mk_Kind_arrow ((Support.List.append bs bs'), k') p)
end
| _ -> begin
(mk_Kind_arrow (bs, k) p)
end)
end)
end))

let mk_Kind_uvar = (fun ( uv ) ( p ) -> (let _68_7406 = (get_unit_ref ())
in (let _68_7405 = (mk_fvs ())
in (let _68_7404 = (mk_uvs ())
in {n = Kind_uvar (uv); tk = _68_7406; pos = p; fvs = _68_7405; uvs = _68_7404}))))

let mk_Kind_lam = (fun ( _20_391 ) ( p ) -> (match (_20_391) with
| (vs, k) -> begin
(let _68_7413 = (get_unit_ref ())
in (let _68_7412 = (mk_fvs ())
in (let _68_7411 = (mk_uvs ())
in {n = Kind_lam ((vs, k)); tk = _68_7413; pos = p; fvs = _68_7412; uvs = _68_7411})))
end))

let mk_Kind_delayed = (fun ( _20_396 ) ( p ) -> (match (_20_396) with
| (k, s, m) -> begin
(let _68_7420 = (get_unit_ref ())
in (let _68_7419 = (mk_fvs ())
in (let _68_7418 = (mk_uvs ())
in {n = Kind_delayed ((k, s, m)); tk = _68_7420; pos = p; fvs = _68_7419; uvs = _68_7418})))
end))

let mk_Kind_unknown = (let _68_7423 = (get_unit_ref ())
in (let _68_7422 = (mk_fvs ())
in (let _68_7421 = (mk_uvs ())
in {n = Kind_unknown; tk = _68_7423; pos = dummyRange; fvs = _68_7422; uvs = _68_7421})))

let get_knd_nref = (fun ( _20_398 ) -> (match (()) with
| () -> begin
(let x = (Support.Microsoft.FStar.Util.mk_ref (Some (mk_Kind_unknown)))
in (let _20_400 = (Support.ST.op_Colon_Equals x None)
in x))
end))

let get_knd_ref = (fun ( k ) -> (let x = (Support.Microsoft.FStar.Util.mk_ref (Some (mk_Kind_unknown)))
in (let _20_404 = (Support.ST.op_Colon_Equals x k)
in x)))

let mk_Typ_btvar = (fun ( x ) ( k ) ( p ) -> (let _68_7436 = (get_knd_ref k)
in (let _68_7435 = (mk_fvs ())
in (let _68_7434 = (mk_uvs ())
in {n = Typ_btvar (x); tk = _68_7436; pos = p; fvs = _68_7435; uvs = _68_7434}))))

let mk_Typ_const = (fun ( x ) ( k ) ( p ) -> (let _68_7443 = (get_knd_ref k)
in {n = Typ_const (x); tk = _68_7443; pos = p; fvs = memo_no_fvs; uvs = memo_no_uvs}))

let rec check_fun = (fun ( bs ) ( c ) ( p ) -> (match (bs) with
| [] -> begin
(failwith ("Empty binders"))
end
| _ -> begin
Typ_fun ((bs, c))
end))

let mk_Typ_fun = (fun ( _20_420 ) ( k ) ( p ) -> (match (_20_420) with
| (bs, c) -> begin
(let _68_7456 = (check_fun bs c p)
in (let _68_7455 = (Support.Microsoft.FStar.Util.mk_ref k)
in (let _68_7454 = (mk_fvs ())
in (let _68_7453 = (mk_uvs ())
in {n = _68_7456; tk = _68_7455; pos = p; fvs = _68_7454; uvs = _68_7453}))))
end))

let mk_Typ_refine = (fun ( _20_425 ) ( k ) ( p ) -> (match (_20_425) with
| (x, phi) -> begin
(let _68_7465 = (Support.Microsoft.FStar.Util.mk_ref k)
in (let _68_7464 = (mk_fvs ())
in (let _68_7463 = (mk_uvs ())
in {n = Typ_refine ((x, phi)); tk = _68_7465; pos = p; fvs = _68_7464; uvs = _68_7463})))
end))

let mk_Typ_app = (fun ( _20_430 ) ( k ) ( p ) -> (match (_20_430) with
| (t1, args) -> begin
(let _68_7475 = (match (args) with
| [] -> begin
(failwith ("Empty arg list!"))
end
| _ -> begin
Typ_app ((t1, args))
end)
in (let _68_7474 = (Support.Microsoft.FStar.Util.mk_ref k)
in (let _68_7473 = (mk_fvs ())
in (let _68_7472 = (mk_uvs ())
in {n = _68_7475; tk = _68_7474; pos = p; fvs = _68_7473; uvs = _68_7472}))))
end))

let mk_Typ_app' = (fun ( _20_438 ) ( k ) ( p ) -> (match (_20_438) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _ -> begin
(mk_Typ_app (t1, args) k p)
end)
end))

let extend_typ_app = (fun ( _20_446 ) ( k ) ( p ) -> (match (_20_446) with
| (t, arg) -> begin
(match (t.n) with
| Typ_app ((h, args)) -> begin
(mk_Typ_app (h, (Support.List.append args ((arg)::[]))) k p)
end
| _ -> begin
(mk_Typ_app (t, (arg)::[]) k p)
end)
end))

let mk_Typ_lam = (fun ( _20_457 ) ( k ) ( p ) -> (match (_20_457) with
| (b, t) -> begin
(let _68_7497 = (match (b) with
| [] -> begin
(failwith ("Empty binders!"))
end
| _ -> begin
Typ_lam ((b, t))
end)
in (let _68_7496 = (Support.Microsoft.FStar.Util.mk_ref k)
in (let _68_7495 = (mk_fvs ())
in (let _68_7494 = (mk_uvs ())
in {n = _68_7497; tk = _68_7496; pos = p; fvs = _68_7495; uvs = _68_7494}))))
end))

let mk_Typ_lam' = (fun ( _20_465 ) ( k ) ( p ) -> (match (_20_465) with
| (bs, t) -> begin
(match (bs) with
| [] -> begin
t
end
| _ -> begin
(mk_Typ_lam (bs, t) k p)
end)
end))

let mk_Typ_ascribed' = (fun ( _20_473 ) ( k' ) ( p ) -> (match (_20_473) with
| (t, k) -> begin
(let _68_7512 = (Support.Microsoft.FStar.Util.mk_ref k')
in (let _68_7511 = (mk_fvs ())
in (let _68_7510 = (mk_uvs ())
in {n = Typ_ascribed ((t, k)); tk = _68_7512; pos = p; fvs = _68_7511; uvs = _68_7510})))
end))

let mk_Typ_ascribed = (fun ( _20_478 ) ( p ) -> (match (_20_478) with
| (t, k) -> begin
(mk_Typ_ascribed' (t, k) (Some (k)) p)
end))

let mk_Typ_meta' = (fun ( m ) ( k ) ( p ) -> (let _68_7525 = (Support.Microsoft.FStar.Util.mk_ref k)
in (let _68_7524 = (mk_fvs ())
in (let _68_7523 = (mk_uvs ())
in {n = Typ_meta (m); tk = _68_7525; pos = p; fvs = _68_7524; uvs = _68_7523}))))

let mk_Typ_meta = (fun ( m ) -> (match (m) with
| (Meta_pattern ((t, _))) | (Meta_named ((t, _))) | (Meta_labeled ((t, _, _, _))) | (Meta_refresh_label ((t, _, _))) | (Meta_slack_formula ((t, _, _))) -> begin
(let _68_7528 = (Support.ST.read t.tk)
in (mk_Typ_meta' m _68_7528 t.pos))
end))

let mk_Typ_uvar' = (fun ( _20_515 ) ( k' ) ( p ) -> (match (_20_515) with
| (u, k) -> begin
(let _68_7537 = (get_knd_ref k')
in (let _68_7536 = (mk_fvs ())
in (let _68_7535 = (mk_uvs ())
in {n = Typ_uvar ((u, k)); tk = _68_7537; pos = p; fvs = _68_7536; uvs = _68_7535})))
end))

let mk_Typ_uvar = (fun ( _20_520 ) ( p ) -> (match (_20_520) with
| (u, k) -> begin
(mk_Typ_uvar' (u, k) (Some (k)) p)
end))

let mk_Typ_delayed = (fun ( _20_525 ) ( k ) ( p ) -> (match (_20_525) with
| (t, s, m) -> begin
(let _68_7554 = (match (t.n) with
| Typ_delayed (_) -> begin
(failwith ("NESTED DELAYED TYPES!"))
end
| _ -> begin
Typ_delayed ((Support.Microsoft.FStar.Util.Inl ((t, s)), m))
end)
in (let _68_7553 = (Support.Microsoft.FStar.Util.mk_ref k)
in (let _68_7552 = (mk_fvs ())
in (let _68_7551 = (mk_uvs ())
in {n = _68_7554; tk = _68_7553; pos = p; fvs = _68_7552; uvs = _68_7551}))))
end))

let mk_Typ_delayed' = (fun ( st ) ( k ) ( p ) -> (let _68_7576 = (let _68_7572 = (let _68_7571 = (Support.Microsoft.FStar.Util.mk_ref None)
in (st, _68_7571))
in Typ_delayed (_68_7572))
in (let _68_7575 = (Support.Microsoft.FStar.Util.mk_ref k)
in (let _68_7574 = (mk_fvs ())
in (let _68_7573 = (mk_uvs ())
in {n = _68_7576; tk = _68_7575; pos = p; fvs = _68_7574; uvs = _68_7573})))))

let mk_Typ_unknown = (let _68_7579 = (get_knd_nref ())
in (let _68_7578 = (mk_fvs ())
in (let _68_7577 = (mk_uvs ())
in {n = Typ_unknown; tk = _68_7579; pos = dummyRange; fvs = _68_7578; uvs = _68_7577})))

let get_typ_nref = (fun ( _20_536 ) -> (match (()) with
| () -> begin
(let x = (Support.Microsoft.FStar.Util.mk_ref (Some (mk_Typ_unknown)))
in (let _20_538 = (Support.ST.op_Colon_Equals x None)
in x))
end))

let get_typ_ref = (fun ( t ) -> (let x = (Support.Microsoft.FStar.Util.mk_ref (Some (mk_Typ_unknown)))
in (let _20_542 = (Support.ST.op_Colon_Equals x t)
in x)))

let mk_Total = (fun ( t ) -> (let _68_7588 = (Support.Microsoft.FStar.Util.mk_ref None)
in (let _68_7587 = (mk_fvs ())
in (let _68_7586 = (mk_uvs ())
in {n = Total (t); tk = _68_7588; pos = t.pos; fvs = _68_7587; uvs = _68_7586}))))

let mk_Comp = (fun ( ct ) -> (let _68_7593 = (Support.Microsoft.FStar.Util.mk_ref None)
in (let _68_7592 = (mk_fvs ())
in (let _68_7591 = (mk_uvs ())
in {n = Comp (ct); tk = _68_7593; pos = ct.result_typ.pos; fvs = _68_7592; uvs = _68_7591}))))

let mk_Exp_bvar = (fun ( x ) ( t ) ( p ) -> (let _68_7602 = (get_typ_ref t)
in (let _68_7601 = (mk_fvs ())
in (let _68_7600 = (mk_uvs ())
in {n = Exp_bvar (x); tk = _68_7602; pos = p; fvs = _68_7601; uvs = _68_7600}))))

let mk_Exp_fvar = (fun ( _20_551 ) ( t ) ( p ) -> (match (_20_551) with
| (x, b) -> begin
(let _68_7611 = (get_typ_ref t)
in (let _68_7610 = (mk_fvs ())
in (let _68_7609 = (mk_uvs ())
in {n = Exp_fvar ((x, b)); tk = _68_7611; pos = p; fvs = _68_7610; uvs = _68_7609})))
end))

let mk_Exp_constant = (fun ( s ) ( t ) ( p ) -> (let _68_7620 = (get_typ_ref t)
in (let _68_7619 = (mk_fvs ())
in (let _68_7618 = (mk_uvs ())
in {n = Exp_constant (s); tk = _68_7620; pos = p; fvs = _68_7619; uvs = _68_7618}))))

let mk_Exp_abs = (fun ( _20_559 ) ( t' ) ( p ) -> (match (_20_559) with
| (b, e) -> begin
(let _68_7630 = (match (b) with
| [] -> begin
(failwith ("abstraction with no binders!"))
end
| _ -> begin
Exp_abs ((b, e))
end)
in (let _68_7629 = (get_typ_ref t')
in (let _68_7628 = (mk_fvs ())
in (let _68_7627 = (mk_uvs ())
in {n = _68_7630; tk = _68_7629; pos = p; fvs = _68_7628; uvs = _68_7627}))))
end))

let mk_Exp_abs' = (fun ( _20_567 ) ( t' ) ( p ) -> (match (_20_567) with
| (b, e) -> begin
(let _68_7640 = (match ((b, e.n)) with
| (_, Exp_abs ((b0::bs, body))) -> begin
Exp_abs (((Support.List.append b ((b0)::bs)), body))
end
| ([], _) -> begin
(failwith ("abstraction with no binders!"))
end
| _ -> begin
Exp_abs ((b, e))
end)
in (let _68_7639 = (get_typ_ref t')
in (let _68_7638 = (mk_fvs ())
in (let _68_7637 = (mk_uvs ())
in {n = _68_7640; tk = _68_7639; pos = p; fvs = _68_7638; uvs = _68_7637}))))
end))

let mk_Exp_app = (fun ( _20_587 ) ( t ) ( p ) -> (match (_20_587) with
| (e1, args) -> begin
(let _68_7650 = (match (args) with
| [] -> begin
(failwith ("Empty args!"))
end
| _ -> begin
Exp_app ((e1, args))
end)
in (let _68_7649 = (get_typ_ref t)
in (let _68_7648 = (mk_fvs ())
in (let _68_7647 = (mk_uvs ())
in {n = _68_7650; tk = _68_7649; pos = p; fvs = _68_7648; uvs = _68_7647}))))
end))

let mk_Exp_app_flat = (fun ( _20_595 ) ( t ) ( p ) -> (match (_20_595) with
| (e1, args) -> begin
(match (e1.n) with
| Exp_app ((e1', args')) -> begin
(mk_Exp_app (e1', (Support.List.append args' args)) t p)
end
| _ -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

let mk_Exp_app' = (fun ( _20_606 ) ( t ) ( p ) -> (match (_20_606) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _ -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

let rec pat_vars = (fun ( p ) -> (match (p.v) with
| Pat_cons ((_, _, ps)) -> begin
(let vars = (Support.List.collect pat_vars ps)
in (match ((Support.Prims.pipe_right vars (Support.Microsoft.FStar.Util.nodups (fun ( x ) ( y ) -> (match ((x, y)) with
| (Support.Microsoft.FStar.Util.Inl (x), Support.Microsoft.FStar.Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(bvd_eq x y)
end
| _ -> begin
false
end))))) with
| true -> begin
vars
end
| false -> begin
(raise (Error (("Pattern variables may not occur more than once", p.p))))
end))
end
| Pat_var ((x, _)) -> begin
(Support.Microsoft.FStar.Util.Inr (x.v))::[]
end
| Pat_tvar (a) -> begin
(Support.Microsoft.FStar.Util.Inl (a.v))::[]
end
| Pat_disj (ps) -> begin
(let vars = (Support.List.map pat_vars ps)
in (match ((not ((let _68_7670 = (Support.List.tl vars)
in (let _68_7669 = (let _68_7668 = (let _68_7667 = (Support.List.hd vars)
in (Support.Microsoft.FStar.Util.set_eq order_bvd _68_7667))
in (Support.Microsoft.FStar.Util.for_all _68_7668))
in (Support.Prims.pipe_right _68_7670 _68_7669)))))) with
| true -> begin
(let vars = (let _68_7674 = (Support.Prims.pipe_right vars (Support.List.map (fun ( v ) -> (let _68_7673 = (Support.List.map (fun ( _20_2 ) -> (match (_20_2) with
| Support.Microsoft.FStar.Util.Inr (x) -> begin
x.ppname.idText
end
| Support.Microsoft.FStar.Util.Inl (x) -> begin
x.ppname.idText
end)) v)
in (Support.Microsoft.FStar.Util.concat_l ", " _68_7673)))))
in (Support.Microsoft.FStar.Util.concat_l ";\n" _68_7674))
in (let _68_7677 = (let _68_7676 = (let _68_7675 = (Support.Microsoft.FStar.Util.format1 "Each branch of this pattern binds different variables: %s" vars)
in (_68_7675, p.p))
in Error (_68_7676))
in (raise (_68_7677))))
end
| false -> begin
(Support.List.hd vars)
end))
end
| (Pat_dot_term (_)) | (Pat_dot_typ (_)) | (Pat_wild (_)) | (Pat_twild (_)) | (Pat_constant (_)) -> begin
[]
end))

let mk_Exp_match = (fun ( _20_669 ) ( t ) ( p ) -> (match (_20_669) with
| (e, pats) -> begin
(let _68_7686 = (get_typ_ref t)
in (let _68_7685 = (mk_fvs ())
in (let _68_7684 = (mk_uvs ())
in {n = Exp_match ((e, pats)); tk = _68_7686; pos = p; fvs = _68_7685; uvs = _68_7684})))
end))

let mk_Exp_ascribed = (fun ( _20_675 ) ( t' ) ( p ) -> (match (_20_675) with
| (e, t, l) -> begin
(let _68_7695 = (get_typ_ref t')
in (let _68_7694 = (mk_fvs ())
in (let _68_7693 = (mk_uvs ())
in {n = Exp_ascribed ((e, t, l)); tk = _68_7695; pos = p; fvs = _68_7694; uvs = _68_7693})))
end))

let mk_Exp_let = (fun ( _20_680 ) ( t ) ( p ) -> (match (_20_680) with
| (lbs, e) -> begin
(let _68_7704 = (get_typ_ref t)
in (let _68_7703 = (mk_fvs ())
in (let _68_7702 = (mk_uvs ())
in {n = Exp_let ((lbs, e)); tk = _68_7704; pos = p; fvs = _68_7703; uvs = _68_7702})))
end))

let mk_Exp_uvar' = (fun ( _20_685 ) ( t' ) ( p ) -> (match (_20_685) with
| (u, t) -> begin
(let _68_7713 = (get_typ_ref t')
in (let _68_7712 = (mk_fvs ())
in (let _68_7711 = (mk_uvs ())
in {n = Exp_uvar ((u, t)); tk = _68_7713; pos = p; fvs = _68_7712; uvs = _68_7711})))
end))

let mk_Exp_uvar = (fun ( _20_690 ) ( p ) -> (match (_20_690) with
| (u, t) -> begin
(mk_Exp_uvar' (u, t) (Some (t)) p)
end))

let mk_Exp_delayed = (fun ( _20_695 ) ( t ) ( p ) -> (match (_20_695) with
| (e, s, m) -> begin
(let _68_7726 = (get_typ_ref t)
in (let _68_7725 = (mk_fvs ())
in (let _68_7724 = (mk_uvs ())
in {n = Exp_delayed ((e, s, m)); tk = _68_7726; pos = p; fvs = _68_7725; uvs = _68_7724})))
end))

let mk_Exp_meta' = (fun ( m ) ( t ) ( p ) -> (let _68_7735 = (get_typ_ref t)
in (let _68_7734 = (mk_fvs ())
in (let _68_7733 = (mk_uvs ())
in {n = Exp_meta (m); tk = _68_7735; pos = p; fvs = _68_7734; uvs = _68_7733}))))

let mk_Exp_meta = (fun ( m ) -> (match (m) with
| Meta_desugared ((e, _)) -> begin
(let _68_7738 = (Support.ST.read e.tk)
in (mk_Exp_meta' m _68_7738 e.pos))
end))

let mk_lb = (fun ( _20_711 ) -> (match (_20_711) with
| (x, eff, t, e) -> begin
{lbname = x; lbtyp = t; lbeff = eff; lbdef = e}
end))

let mk_subst = (fun ( s ) -> s)

let extend_subst = (fun ( x ) ( s ) -> (x)::s)

let argpos = (fun ( x ) -> (match (x) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
t.pos
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
e.pos
end))

let tun = mk_Typ_unknown

let kun = mk_Kind_unknown

let ktype = mk_Kind_type

let keffect = mk_Kind_effect

let null_id = (mk_ident ("_", dummyRange))

let null_bvd = {ppname = null_id; realname = null_id}

let null_bvar = (fun ( k ) -> {v = null_bvd; sort = k; p = dummyRange})

let t_binder = (fun ( a ) -> (Support.Microsoft.FStar.Util.Inl (a), None))

let v_binder = (fun ( a ) -> (Support.Microsoft.FStar.Util.Inr (a), None))

let null_t_binder = (fun ( t ) -> (let _68_7757 = (let _68_7756 = (null_bvar t)
in Support.Microsoft.FStar.Util.Inl (_68_7756))
in (_68_7757, None)))

let null_v_binder = (fun ( t ) -> (let _68_7761 = (let _68_7760 = (null_bvar t)
in Support.Microsoft.FStar.Util.Inr (_68_7760))
in (_68_7761, None)))

let itarg = (fun ( t ) -> (Support.Microsoft.FStar.Util.Inl (t), Some (Implicit)))

let ivarg = (fun ( v ) -> (Support.Microsoft.FStar.Util.Inr (v), Some (Implicit)))

let targ = (fun ( t ) -> (Support.Microsoft.FStar.Util.Inl (t), None))

let varg = (fun ( v ) -> (Support.Microsoft.FStar.Util.Inr (v), None))

let is_null_pp = (fun ( b ) -> (b.ppname.idText = null_id.idText))

let is_null_bvd = (fun ( b ) -> (b.realname.idText = null_id.idText))

let is_null_bvar = (fun ( b ) -> (is_null_bvd b.v))

let is_null_binder = (fun ( b ) -> (match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), _) -> begin
(is_null_bvar a)
end
| (Support.Microsoft.FStar.Util.Inr (x), _) -> begin
(is_null_bvar x)
end))

let freevars_of_binders = (fun ( bs ) -> (Support.Prims.pipe_right bs (Support.List.fold_left (fun ( out ) ( _20_3 ) -> (match (_20_3) with
| (Support.Microsoft.FStar.Util.Inl (btv), _) -> begin
(let _20_761 = out
in (let _68_7782 = (Support.Microsoft.FStar.Util.set_add btv out.ftvs)
in {ftvs = _68_7782; fxvs = _20_761.fxvs}))
end
| (Support.Microsoft.FStar.Util.Inr (bxv), _) -> begin
(let _20_768 = out
in (let _68_7783 = (Support.Microsoft.FStar.Util.set_add bxv out.fxvs)
in {ftvs = _20_768.ftvs; fxvs = _68_7783}))
end)) no_fvs)))

let binders_of_list = (fun ( fvs ) -> (Support.Prims.pipe_right fvs (Support.List.map (fun ( t ) -> (t, None)))))

let binders_of_freevars = (fun ( fvs ) -> (let _68_7792 = (let _68_7789 = (Support.Microsoft.FStar.Util.set_elements fvs.ftvs)
in (Support.Prims.pipe_right _68_7789 (Support.List.map t_binder)))
in (let _68_7791 = (let _68_7790 = (Support.Microsoft.FStar.Util.set_elements fvs.fxvs)
in (Support.Prims.pipe_right _68_7790 (Support.List.map v_binder)))
in (Support.List.append _68_7792 _68_7791))))

let is_implicit = (fun ( _20_4 ) -> (match (_20_4) with
| Some (Implicit) -> begin
true
end
| _ -> begin
false
end))

let as_implicit = (fun ( _20_5 ) -> (match (_20_5) with
| true -> begin
Some (Implicit)
end
| _ -> begin
None
end))




