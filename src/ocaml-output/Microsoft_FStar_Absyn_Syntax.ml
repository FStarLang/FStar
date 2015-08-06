
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

let is_Mkident = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkident"))

type l__LongIdent =
{ns : ident list; ident : ident; nsstr : string; str : string}

let is_MkLongIdent = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_MkLongIdent"))

type lident =
l__LongIdent

type ('a, 't) withinfo_t =
{v : 'a; sort : 't; p : Support.Microsoft.FStar.Range.range}

let is_Mkwithinfo_t = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkwithinfo_t"))

type 't var =
(lident, 't) withinfo_t

type fieldname =
lident

type 'a bvdef =
{ppname : ident; realname : ident}

let is_Mkbvdef = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkbvdef"))

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
'a option Support.ST.ref

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
| Meta_slack_formula of (typ * typ * bool Support.ST.ref) 
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

let is_Mkcomp_typ = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkcomp_typ"))

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

let is_Mkletbinding = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkletbinding"))

let is_Mkfreevars = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkfreevars"))

let is_Mkuvars = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkuvars"))

let is_Mksyntax = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mksyntax"))

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

let is_Mkmonad_abbrev = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkmonad_abbrev"))

type sub_eff =
{source : lident; target : lident; lift : typ}

let is_Mksub_eff = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mksub_eff"))

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

let is_Mkeff_decl = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkeff_decl"))

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

let is_Mkmodul = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkmodul"))

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

let is_Mklcomp = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mklcomp"))

type path =
string list

let dummyRange = 0L

let withinfo = (fun ( v ) ( s ) ( r ) -> {v = v; sort = s; p = r})

let withsort = (fun ( v ) ( s ) -> (withinfo v s dummyRange))

let mk_ident = (fun ( _22_261 ) -> (match (_22_261) with
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

let lid_of_ids = (fun ( ids ) -> (let _22_272 = (Support.Microsoft.FStar.Util.prefix ids)
in (match (_22_272) with
| (ns, id) -> begin
(let nsstr = (let _70_7427 = (Support.List.map text_of_id ns)
in (Support.All.pipe_right _70_7427 text_of_path))
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
| (Support.Microsoft.FStar.Util.Inl (_22_287), Support.Microsoft.FStar.Util.Inr (_22_290)) -> begin
(- (1))
end
| (Support.Microsoft.FStar.Util.Inr (_22_294), Support.Microsoft.FStar.Util.Inl (_22_297)) -> begin
1
end
| (Support.Microsoft.FStar.Util.Inl (x), Support.Microsoft.FStar.Util.Inl (y)) -> begin
(Support.String.compare x.realname.idText y.realname.idText)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(Support.String.compare x.realname.idText y.realname.idText)
end))

let lid_with_range = (fun ( lid ) ( r ) -> (let id = (let _22_312 = lid.ident
in {idText = _22_312.idText; idRange = r})
in (let _22_315 = lid
in {ns = _22_315.ns; ident = id; nsstr = _22_315.nsstr; str = _22_315.str})))

let range_of_lid = (fun ( lid ) -> lid.ident.idRange)

let range_of_lbname = (fun ( l ) -> (match (l) with
| Support.Microsoft.FStar.Util.Inl (x) -> begin
x.ppname.idRange
end
| Support.Microsoft.FStar.Util.Inr (l) -> begin
(range_of_lid l)
end))

let syn = (fun ( p ) ( k ) ( f ) -> (f k p))

let mk_fvs = (fun ( _22_326 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.mk_ref None)
end))

let mk_uvs = (fun ( _22_327 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.mk_ref None)
end))

let new_ftv_set = (fun ( _22_328 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.new_set (fun ( x ) ( y ) -> (Support.Microsoft.FStar.Util.compare x.v.realname.idText y.v.realname.idText)) (fun ( x ) -> (Support.Microsoft.FStar.Util.hashcode x.v.realname.idText)))
end))

let new_uv_set = (fun ( _22_332 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.new_set (fun ( x ) ( y ) -> ((Support.Microsoft.FStar.Unionfind.uvar_id x) - (Support.Microsoft.FStar.Unionfind.uvar_id y))) Support.Microsoft.FStar.Unionfind.uvar_id)
end))

let new_uvt_set = (fun ( _22_335 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.new_set (fun ( _22_343 ) ( _22_347 ) -> (match ((_22_343, _22_347)) with
| ((x, _22_342), (y, _22_346)) -> begin
((Support.Microsoft.FStar.Unionfind.uvar_id x) - (Support.Microsoft.FStar.Unionfind.uvar_id y))
end)) (fun ( _22_339 ) -> (match (_22_339) with
| (x, _22_338) -> begin
(Support.Microsoft.FStar.Unionfind.uvar_id x)
end)))
end))

let no_fvs = (let _70_7476 = (new_ftv_set ())
in (let _70_7475 = (new_ftv_set ())
in {ftvs = _70_7476; fxvs = _70_7475}))

let no_uvs = (let _70_7479 = (new_uv_set ())
in (let _70_7478 = (new_uvt_set ())
in (let _70_7477 = (new_uvt_set ())
in {uvars_k = _70_7479; uvars_t = _70_7478; uvars_e = _70_7477})))

let memo_no_uvs = (Support.Microsoft.FStar.Util.mk_ref (Some (no_uvs)))

let memo_no_fvs = (Support.Microsoft.FStar.Util.mk_ref (Some (no_fvs)))

let freevars_of_list = (fun ( l ) -> (Support.All.pipe_right l (Support.List.fold_left (fun ( out ) ( _22_1 ) -> (match (_22_1) with
| Support.Microsoft.FStar.Util.Inl (btv) -> begin
(let _22_353 = out
in (let _70_7484 = (Support.Microsoft.FStar.Util.set_add btv out.ftvs)
in {ftvs = _70_7484; fxvs = _22_353.fxvs}))
end
| Support.Microsoft.FStar.Util.Inr (bxv) -> begin
(let _22_357 = out
in (let _70_7485 = (Support.Microsoft.FStar.Util.set_add bxv out.fxvs)
in {ftvs = _22_357.ftvs; fxvs = _70_7485}))
end)) no_fvs)))

let list_of_freevars = (fun ( fvs ) -> (let _70_7493 = (let _70_7489 = (Support.Microsoft.FStar.Util.set_elements fvs.ftvs)
in (Support.All.pipe_right _70_7489 (Support.List.map (fun ( x ) -> Support.Microsoft.FStar.Util.Inl (x)))))
in (let _70_7492 = (let _70_7491 = (Support.Microsoft.FStar.Util.set_elements fvs.fxvs)
in (Support.All.pipe_right _70_7491 (Support.List.map (fun ( x ) -> Support.Microsoft.FStar.Util.Inr (x)))))
in (Support.List.append _70_7493 _70_7492))))

let get_unit_ref = (fun ( _22_362 ) -> (match (()) with
| () -> begin
(let x = (Support.Microsoft.FStar.Util.mk_ref (Some (())))
in (let _22_364 = (Support.ST.op_Colon_Equals x None)
in x))
end))

let mk_Kind_type = (let _70_7498 = (get_unit_ref ())
in (let _70_7497 = (mk_fvs ())
in (let _70_7496 = (mk_uvs ())
in {n = Kind_type; tk = _70_7498; pos = dummyRange; fvs = _70_7497; uvs = _70_7496})))

let mk_Kind_effect = (let _70_7501 = (get_unit_ref ())
in (let _70_7500 = (mk_fvs ())
in (let _70_7499 = (mk_uvs ())
in {n = Kind_effect; tk = _70_7501; pos = dummyRange; fvs = _70_7500; uvs = _70_7499})))

let mk_Kind_abbrev = (fun ( _22_368 ) ( p ) -> (match (_22_368) with
| (kabr, k) -> begin
(let _70_7508 = (get_unit_ref ())
in (let _70_7507 = (mk_fvs ())
in (let _70_7506 = (mk_uvs ())
in {n = Kind_abbrev ((kabr, k)); tk = _70_7508; pos = p; fvs = _70_7507; uvs = _70_7506})))
end))

let mk_Kind_arrow = (fun ( _22_372 ) ( p ) -> (match (_22_372) with
| (bs, k) -> begin
(let _70_7515 = (get_unit_ref ())
in (let _70_7514 = (mk_fvs ())
in (let _70_7513 = (mk_uvs ())
in {n = Kind_arrow ((bs, k)); tk = _70_7515; pos = p; fvs = _70_7514; uvs = _70_7513})))
end))

let mk_Kind_arrow' = (fun ( _22_376 ) ( p ) -> (match (_22_376) with
| (bs, k) -> begin
(match (bs) with
| [] -> begin
k
end
| _22_380 -> begin
(match (k.n) with
| Kind_arrow ((bs', k')) -> begin
(mk_Kind_arrow ((Support.List.append bs bs'), k') p)
end
| _22_386 -> begin
(mk_Kind_arrow (bs, k) p)
end)
end)
end))

let mk_Kind_uvar = (fun ( uv ) ( p ) -> (let _70_7526 = (get_unit_ref ())
in (let _70_7525 = (mk_fvs ())
in (let _70_7524 = (mk_uvs ())
in {n = Kind_uvar (uv); tk = _70_7526; pos = p; fvs = _70_7525; uvs = _70_7524}))))

let mk_Kind_lam = (fun ( _22_391 ) ( p ) -> (match (_22_391) with
| (vs, k) -> begin
(let _70_7533 = (get_unit_ref ())
in (let _70_7532 = (mk_fvs ())
in (let _70_7531 = (mk_uvs ())
in {n = Kind_lam ((vs, k)); tk = _70_7533; pos = p; fvs = _70_7532; uvs = _70_7531})))
end))

let mk_Kind_delayed = (fun ( _22_396 ) ( p ) -> (match (_22_396) with
| (k, s, m) -> begin
(let _70_7540 = (get_unit_ref ())
in (let _70_7539 = (mk_fvs ())
in (let _70_7538 = (mk_uvs ())
in {n = Kind_delayed ((k, s, m)); tk = _70_7540; pos = p; fvs = _70_7539; uvs = _70_7538})))
end))

let mk_Kind_unknown = (let _70_7543 = (get_unit_ref ())
in (let _70_7542 = (mk_fvs ())
in (let _70_7541 = (mk_uvs ())
in {n = Kind_unknown; tk = _70_7543; pos = dummyRange; fvs = _70_7542; uvs = _70_7541})))

let get_knd_nref = (fun ( _22_398 ) -> (match (()) with
| () -> begin
(let x = (Support.Microsoft.FStar.Util.mk_ref (Some (mk_Kind_unknown)))
in (let _22_400 = (Support.ST.op_Colon_Equals x None)
in x))
end))

let get_knd_ref = (fun ( k ) -> (let x = (Support.Microsoft.FStar.Util.mk_ref (Some (mk_Kind_unknown)))
in (let _22_404 = (Support.ST.op_Colon_Equals x k)
in x)))

let mk_Typ_btvar = (fun ( x ) ( k ) ( p ) -> (let _70_7556 = (get_knd_ref k)
in (let _70_7555 = (mk_fvs ())
in (let _70_7554 = (mk_uvs ())
in {n = Typ_btvar (x); tk = _70_7556; pos = p; fvs = _70_7555; uvs = _70_7554}))))

let mk_Typ_const = (fun ( x ) ( k ) ( p ) -> (let _70_7563 = (get_knd_ref k)
in {n = Typ_const (x); tk = _70_7563; pos = p; fvs = memo_no_fvs; uvs = memo_no_uvs}))

let rec check_fun = (fun ( bs ) ( c ) ( p ) -> (match (bs) with
| [] -> begin
(Support.All.failwith "Empty binders")
end
| _22_417 -> begin
Typ_fun ((bs, c))
end))

let mk_Typ_fun = (fun ( _22_420 ) ( k ) ( p ) -> (match (_22_420) with
| (bs, c) -> begin
(let _70_7576 = (check_fun bs c p)
in (let _70_7575 = (Support.Microsoft.FStar.Util.mk_ref k)
in (let _70_7574 = (mk_fvs ())
in (let _70_7573 = (mk_uvs ())
in {n = _70_7576; tk = _70_7575; pos = p; fvs = _70_7574; uvs = _70_7573}))))
end))

let mk_Typ_refine = (fun ( _22_425 ) ( k ) ( p ) -> (match (_22_425) with
| (x, phi) -> begin
(let _70_7585 = (Support.Microsoft.FStar.Util.mk_ref k)
in (let _70_7584 = (mk_fvs ())
in (let _70_7583 = (mk_uvs ())
in {n = Typ_refine ((x, phi)); tk = _70_7585; pos = p; fvs = _70_7584; uvs = _70_7583})))
end))

let mk_Typ_app = (fun ( _22_430 ) ( k ) ( p ) -> (match (_22_430) with
| (t1, args) -> begin
(let _70_7595 = (match (args) with
| [] -> begin
(Support.All.failwith "Empty arg list!")
end
| _22_435 -> begin
Typ_app ((t1, args))
end)
in (let _70_7594 = (Support.Microsoft.FStar.Util.mk_ref k)
in (let _70_7593 = (mk_fvs ())
in (let _70_7592 = (mk_uvs ())
in {n = _70_7595; tk = _70_7594; pos = p; fvs = _70_7593; uvs = _70_7592}))))
end))

let mk_Typ_app' = (fun ( _22_438 ) ( k ) ( p ) -> (match (_22_438) with
| (t1, args) -> begin
(match (args) with
| [] -> begin
t1
end
| _22_443 -> begin
(mk_Typ_app (t1, args) k p)
end)
end))

let extend_typ_app = (fun ( _22_446 ) ( k ) ( p ) -> (match (_22_446) with
| (t, arg) -> begin
(match (t.n) with
| Typ_app ((h, args)) -> begin
(mk_Typ_app (h, (Support.List.append args ((arg)::[]))) k p)
end
| _22_454 -> begin
(mk_Typ_app (t, (arg)::[]) k p)
end)
end))

let mk_Typ_lam = (fun ( _22_457 ) ( k ) ( p ) -> (match (_22_457) with
| (b, t) -> begin
(let _70_7617 = (match (b) with
| [] -> begin
(Support.All.failwith "Empty binders!")
end
| _22_462 -> begin
Typ_lam ((b, t))
end)
in (let _70_7616 = (Support.Microsoft.FStar.Util.mk_ref k)
in (let _70_7615 = (mk_fvs ())
in (let _70_7614 = (mk_uvs ())
in {n = _70_7617; tk = _70_7616; pos = p; fvs = _70_7615; uvs = _70_7614}))))
end))

let mk_Typ_lam' = (fun ( _22_465 ) ( k ) ( p ) -> (match (_22_465) with
| (bs, t) -> begin
(match (bs) with
| [] -> begin
t
end
| _22_470 -> begin
(mk_Typ_lam (bs, t) k p)
end)
end))

let mk_Typ_ascribed' = (fun ( _22_473 ) ( k' ) ( p ) -> (match (_22_473) with
| (t, k) -> begin
(let _70_7632 = (Support.Microsoft.FStar.Util.mk_ref k')
in (let _70_7631 = (mk_fvs ())
in (let _70_7630 = (mk_uvs ())
in {n = Typ_ascribed ((t, k)); tk = _70_7632; pos = p; fvs = _70_7631; uvs = _70_7630})))
end))

let mk_Typ_ascribed = (fun ( _22_478 ) ( p ) -> (match (_22_478) with
| (t, k) -> begin
(mk_Typ_ascribed' (t, k) (Some (k)) p)
end))

let mk_Typ_meta' = (fun ( m ) ( k ) ( p ) -> (let _70_7645 = (Support.Microsoft.FStar.Util.mk_ref k)
in (let _70_7644 = (mk_fvs ())
in (let _70_7643 = (mk_uvs ())
in {n = Typ_meta (m); tk = _70_7645; pos = p; fvs = _70_7644; uvs = _70_7643}))))

let mk_Typ_meta = (fun ( m ) -> (match (m) with
| (Meta_pattern ((t, _))) | (Meta_named ((t, _))) | (Meta_labeled ((t, _, _, _))) | (Meta_refresh_label ((t, _, _))) | (Meta_slack_formula ((t, _, _))) -> begin
(let _70_7648 = (Support.ST.read t.tk)
in (mk_Typ_meta' m _70_7648 t.pos))
end))

let mk_Typ_uvar' = (fun ( _22_515 ) ( k' ) ( p ) -> (match (_22_515) with
| (u, k) -> begin
(let _70_7657 = (get_knd_ref k')
in (let _70_7656 = (mk_fvs ())
in (let _70_7655 = (mk_uvs ())
in {n = Typ_uvar ((u, k)); tk = _70_7657; pos = p; fvs = _70_7656; uvs = _70_7655})))
end))

let mk_Typ_uvar = (fun ( _22_520 ) ( p ) -> (match (_22_520) with
| (u, k) -> begin
(mk_Typ_uvar' (u, k) (Some (k)) p)
end))

let mk_Typ_delayed = (fun ( _22_525 ) ( k ) ( p ) -> (match (_22_525) with
| (t, s, m) -> begin
(let _70_7677 = (match (t.n) with
| Typ_delayed (_22_529) -> begin
(Support.All.failwith "NESTED DELAYED TYPES!")
end
| _22_532 -> begin
Typ_delayed ((Support.Microsoft.FStar.Util.Inl ((t, s)), m))
end)
in (let _70_7676 = (Support.Microsoft.FStar.Util.mk_ref k)
in (let _70_7675 = (mk_fvs ())
in (let _70_7674 = (mk_uvs ())
in {n = _70_7677; tk = _70_7676; pos = p; fvs = _70_7675; uvs = _70_7674}))))
end))

let mk_Typ_delayed' = (fun ( st ) ( k ) ( p ) -> (let _70_7699 = (let _70_7695 = (let _70_7694 = (Support.Microsoft.FStar.Util.mk_ref None)
in (st, _70_7694))
in Typ_delayed (_70_7695))
in (let _70_7698 = (Support.Microsoft.FStar.Util.mk_ref k)
in (let _70_7697 = (mk_fvs ())
in (let _70_7696 = (mk_uvs ())
in {n = _70_7699; tk = _70_7698; pos = p; fvs = _70_7697; uvs = _70_7696})))))

let mk_Typ_unknown = (let _70_7702 = (get_knd_nref ())
in (let _70_7701 = (mk_fvs ())
in (let _70_7700 = (mk_uvs ())
in {n = Typ_unknown; tk = _70_7702; pos = dummyRange; fvs = _70_7701; uvs = _70_7700})))

let get_typ_nref = (fun ( _22_536 ) -> (match (()) with
| () -> begin
(let x = (Support.Microsoft.FStar.Util.mk_ref (Some (mk_Typ_unknown)))
in (let _22_538 = (Support.ST.op_Colon_Equals x None)
in x))
end))

let get_typ_ref = (fun ( t ) -> (let x = (Support.Microsoft.FStar.Util.mk_ref (Some (mk_Typ_unknown)))
in (let _22_542 = (Support.ST.op_Colon_Equals x t)
in x)))

let mk_Total = (fun ( t ) -> (let _70_7711 = (Support.Microsoft.FStar.Util.mk_ref None)
in (let _70_7710 = (mk_fvs ())
in (let _70_7709 = (mk_uvs ())
in {n = Total (t); tk = _70_7711; pos = t.pos; fvs = _70_7710; uvs = _70_7709}))))

let mk_Comp = (fun ( ct ) -> (let _70_7716 = (Support.Microsoft.FStar.Util.mk_ref None)
in (let _70_7715 = (mk_fvs ())
in (let _70_7714 = (mk_uvs ())
in {n = Comp (ct); tk = _70_7716; pos = ct.result_typ.pos; fvs = _70_7715; uvs = _70_7714}))))

let mk_Exp_bvar = (fun ( x ) ( t ) ( p ) -> (let _70_7725 = (get_typ_ref t)
in (let _70_7724 = (mk_fvs ())
in (let _70_7723 = (mk_uvs ())
in {n = Exp_bvar (x); tk = _70_7725; pos = p; fvs = _70_7724; uvs = _70_7723}))))

let mk_Exp_fvar = (fun ( _22_551 ) ( t ) ( p ) -> (match (_22_551) with
| (x, b) -> begin
(let _70_7734 = (get_typ_ref t)
in (let _70_7733 = (mk_fvs ())
in (let _70_7732 = (mk_uvs ())
in {n = Exp_fvar ((x, b)); tk = _70_7734; pos = p; fvs = _70_7733; uvs = _70_7732})))
end))

let mk_Exp_constant = (fun ( s ) ( t ) ( p ) -> (let _70_7743 = (get_typ_ref t)
in (let _70_7742 = (mk_fvs ())
in (let _70_7741 = (mk_uvs ())
in {n = Exp_constant (s); tk = _70_7743; pos = p; fvs = _70_7742; uvs = _70_7741}))))

let mk_Exp_abs = (fun ( _22_559 ) ( t' ) ( p ) -> (match (_22_559) with
| (b, e) -> begin
(let _70_7753 = (match (b) with
| [] -> begin
(Support.All.failwith "abstraction with no binders!")
end
| _22_564 -> begin
Exp_abs ((b, e))
end)
in (let _70_7752 = (get_typ_ref t')
in (let _70_7751 = (mk_fvs ())
in (let _70_7750 = (mk_uvs ())
in {n = _70_7753; tk = _70_7752; pos = p; fvs = _70_7751; uvs = _70_7750}))))
end))

let mk_Exp_abs' = (fun ( _22_567 ) ( t' ) ( p ) -> (match (_22_567) with
| (b, e) -> begin
(let _70_7763 = (match ((b, e.n)) with
| (_22_571, Exp_abs ((b0::bs, body))) -> begin
Exp_abs (((Support.List.append b ((b0)::bs)), body))
end
| ([], _22_581) -> begin
(Support.All.failwith "abstraction with no binders!")
end
| _22_584 -> begin
Exp_abs ((b, e))
end)
in (let _70_7762 = (get_typ_ref t')
in (let _70_7761 = (mk_fvs ())
in (let _70_7760 = (mk_uvs ())
in {n = _70_7763; tk = _70_7762; pos = p; fvs = _70_7761; uvs = _70_7760}))))
end))

let mk_Exp_app = (fun ( _22_587 ) ( t ) ( p ) -> (match (_22_587) with
| (e1, args) -> begin
(let _70_7773 = (match (args) with
| [] -> begin
(Support.All.failwith "Empty args!")
end
| _22_592 -> begin
Exp_app ((e1, args))
end)
in (let _70_7772 = (get_typ_ref t)
in (let _70_7771 = (mk_fvs ())
in (let _70_7770 = (mk_uvs ())
in {n = _70_7773; tk = _70_7772; pos = p; fvs = _70_7771; uvs = _70_7770}))))
end))

let mk_Exp_app_flat = (fun ( _22_595 ) ( t ) ( p ) -> (match (_22_595) with
| (e1, args) -> begin
(match (e1.n) with
| Exp_app ((e1', args')) -> begin
(mk_Exp_app (e1', (Support.List.append args' args)) t p)
end
| _22_603 -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

let mk_Exp_app' = (fun ( _22_606 ) ( t ) ( p ) -> (match (_22_606) with
| (e1, args) -> begin
(match (args) with
| [] -> begin
e1
end
| _22_611 -> begin
(mk_Exp_app (e1, args) t p)
end)
end))

let rec pat_vars = (fun ( p ) -> (match (p.v) with
| Pat_cons ((_22_614, _22_616, ps)) -> begin
(let vars = (Support.List.collect pat_vars ps)
in (match ((Support.All.pipe_right vars (Support.Microsoft.FStar.Util.nodups (fun ( x ) ( y ) -> (match ((x, y)) with
| (Support.Microsoft.FStar.Util.Inl (x), Support.Microsoft.FStar.Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(bvd_eq x y)
end
| _22_634 -> begin
false
end))))) with
| true -> begin
vars
end
| false -> begin
(raise (Error (("Pattern variables may not occur more than once", p.p))))
end))
end
| Pat_var ((x, _22_637)) -> begin
(Support.Microsoft.FStar.Util.Inr (x.v))::[]
end
| Pat_tvar (a) -> begin
(Support.Microsoft.FStar.Util.Inl (a.v))::[]
end
| Pat_disj (ps) -> begin
(let vars = (Support.List.map pat_vars ps)
in (match ((not ((let _70_7793 = (Support.List.tl vars)
in (let _70_7792 = (let _70_7791 = (let _70_7790 = (Support.List.hd vars)
in (Support.Microsoft.FStar.Util.set_eq order_bvd _70_7790))
in (Support.Microsoft.FStar.Util.for_all _70_7791))
in (Support.All.pipe_right _70_7793 _70_7792)))))) with
| true -> begin
(let vars = (let _70_7797 = (Support.All.pipe_right vars (Support.List.map (fun ( v ) -> (let _70_7796 = (Support.List.map (fun ( _22_2 ) -> (match (_22_2) with
| Support.Microsoft.FStar.Util.Inr (x) -> begin
x.ppname.idText
end
| Support.Microsoft.FStar.Util.Inl (x) -> begin
x.ppname.idText
end)) v)
in (Support.Microsoft.FStar.Util.concat_l ", " _70_7796)))))
in (Support.Microsoft.FStar.Util.concat_l ";\n" _70_7797))
in (let _70_7800 = (let _70_7799 = (let _70_7798 = (Support.Microsoft.FStar.Util.format1 "Each branch of this pattern binds different variables: %s" vars)
in (_70_7798, p.p))
in Error (_70_7799))
in (raise (_70_7800))))
end
| false -> begin
(Support.List.hd vars)
end))
end
| (Pat_dot_term (_)) | (Pat_dot_typ (_)) | (Pat_wild (_)) | (Pat_twild (_)) | (Pat_constant (_)) -> begin
[]
end))

let mk_Exp_match = (fun ( _22_669 ) ( t ) ( p ) -> (match (_22_669) with
| (e, pats) -> begin
(let _70_7809 = (get_typ_ref t)
in (let _70_7808 = (mk_fvs ())
in (let _70_7807 = (mk_uvs ())
in {n = Exp_match ((e, pats)); tk = _70_7809; pos = p; fvs = _70_7808; uvs = _70_7807})))
end))

let mk_Exp_ascribed = (fun ( _22_675 ) ( t' ) ( p ) -> (match (_22_675) with
| (e, t, l) -> begin
(let _70_7818 = (get_typ_ref t')
in (let _70_7817 = (mk_fvs ())
in (let _70_7816 = (mk_uvs ())
in {n = Exp_ascribed ((e, t, l)); tk = _70_7818; pos = p; fvs = _70_7817; uvs = _70_7816})))
end))

let mk_Exp_let = (fun ( _22_680 ) ( t ) ( p ) -> (match (_22_680) with
| (lbs, e) -> begin
(let _70_7827 = (get_typ_ref t)
in (let _70_7826 = (mk_fvs ())
in (let _70_7825 = (mk_uvs ())
in {n = Exp_let ((lbs, e)); tk = _70_7827; pos = p; fvs = _70_7826; uvs = _70_7825})))
end))

let mk_Exp_uvar' = (fun ( _22_685 ) ( t' ) ( p ) -> (match (_22_685) with
| (u, t) -> begin
(let _70_7836 = (get_typ_ref t')
in (let _70_7835 = (mk_fvs ())
in (let _70_7834 = (mk_uvs ())
in {n = Exp_uvar ((u, t)); tk = _70_7836; pos = p; fvs = _70_7835; uvs = _70_7834})))
end))

let mk_Exp_uvar = (fun ( _22_690 ) ( p ) -> (match (_22_690) with
| (u, t) -> begin
(mk_Exp_uvar' (u, t) (Some (t)) p)
end))

let mk_Exp_delayed = (fun ( _22_695 ) ( t ) ( p ) -> (match (_22_695) with
| (e, s, m) -> begin
(let _70_7849 = (get_typ_ref t)
in (let _70_7848 = (mk_fvs ())
in (let _70_7847 = (mk_uvs ())
in {n = Exp_delayed ((e, s, m)); tk = _70_7849; pos = p; fvs = _70_7848; uvs = _70_7847})))
end))

let mk_Exp_meta' = (fun ( m ) ( t ) ( p ) -> (let _70_7858 = (get_typ_ref t)
in (let _70_7857 = (mk_fvs ())
in (let _70_7856 = (mk_uvs ())
in {n = Exp_meta (m); tk = _70_7858; pos = p; fvs = _70_7857; uvs = _70_7856}))))

let mk_Exp_meta = (fun ( m ) -> (match (m) with
| Meta_desugared ((e, _22_704)) -> begin
(let _70_7861 = (Support.ST.read e.tk)
in (mk_Exp_meta' m _70_7861 e.pos))
end))

let mk_lb = (fun ( _22_711 ) -> (match (_22_711) with
| (x, eff, t, e) -> begin
{lbname = x; lbtyp = t; lbeff = eff; lbdef = e}
end))

let mk_subst = (fun ( s ) -> s)

let extend_subst = (fun ( x ) ( s ) -> (x)::s)

let argpos = (fun ( x ) -> (match (x) with
| (Support.Microsoft.FStar.Util.Inl (t), _22_719) -> begin
t.pos
end
| (Support.Microsoft.FStar.Util.Inr (e), _22_724) -> begin
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

let null_t_binder = (fun ( t ) -> (let _70_7880 = (let _70_7879 = (null_bvar t)
in Support.Microsoft.FStar.Util.Inl (_70_7879))
in (_70_7880, None)))

let null_v_binder = (fun ( t ) -> (let _70_7884 = (let _70_7883 = (null_bvar t)
in Support.Microsoft.FStar.Util.Inr (_70_7883))
in (_70_7884, None)))

let itarg = (fun ( t ) -> (Support.Microsoft.FStar.Util.Inl (t), Some (Implicit)))

let ivarg = (fun ( v ) -> (Support.Microsoft.FStar.Util.Inr (v), Some (Implicit)))

let targ = (fun ( t ) -> (Support.Microsoft.FStar.Util.Inl (t), None))

let varg = (fun ( v ) -> (Support.Microsoft.FStar.Util.Inr (v), None))

let is_null_pp = (fun ( b ) -> (b.ppname.idText = null_id.idText))

let is_null_bvd = (fun ( b ) -> (b.realname.idText = null_id.idText))

let is_null_bvar = (fun ( b ) -> (is_null_bvd b.v))

let is_null_binder = (fun ( b ) -> (match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), _22_746) -> begin
(is_null_bvar a)
end
| (Support.Microsoft.FStar.Util.Inr (x), _22_751) -> begin
(is_null_bvar x)
end))

let freevars_of_binders = (fun ( bs ) -> (Support.All.pipe_right bs (Support.List.fold_left (fun ( out ) ( _22_3 ) -> (match (_22_3) with
| (Support.Microsoft.FStar.Util.Inl (btv), _22_759) -> begin
(let _22_761 = out
in (let _70_7905 = (Support.Microsoft.FStar.Util.set_add btv out.ftvs)
in {ftvs = _70_7905; fxvs = _22_761.fxvs}))
end
| (Support.Microsoft.FStar.Util.Inr (bxv), _22_766) -> begin
(let _22_768 = out
in (let _70_7906 = (Support.Microsoft.FStar.Util.set_add bxv out.fxvs)
in {ftvs = _22_768.ftvs; fxvs = _70_7906}))
end)) no_fvs)))

let binders_of_list = (fun ( fvs ) -> (Support.All.pipe_right fvs (Support.List.map (fun ( t ) -> (t, None)))))

let binders_of_freevars = (fun ( fvs ) -> (let _70_7915 = (let _70_7912 = (Support.Microsoft.FStar.Util.set_elements fvs.ftvs)
in (Support.All.pipe_right _70_7912 (Support.List.map t_binder)))
in (let _70_7914 = (let _70_7913 = (Support.Microsoft.FStar.Util.set_elements fvs.fxvs)
in (Support.All.pipe_right _70_7913 (Support.List.map v_binder)))
in (Support.List.append _70_7915 _70_7914))))

let is_implicit = (fun ( _22_4 ) -> (match (_22_4) with
| Some (Implicit) -> begin
true
end
| _22_777 -> begin
false
end))

let as_implicit = (fun ( _22_5 ) -> (match (_22_5) with
| true -> begin
Some (Implicit)
end
| _22_781 -> begin
None
end))




