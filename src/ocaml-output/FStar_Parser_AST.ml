
open Prims
type level =
| Un
| Expr
| Type
| Kind
| Formula

let is_Un = (fun _discr_ -> (match (_discr_) with
| Un -> begin
true
end
| _ -> begin
false
end))

let is_Expr = (fun _discr_ -> (match (_discr_) with
| Expr -> begin
true
end
| _ -> begin
false
end))

let is_Type = (fun _discr_ -> (match (_discr_) with
| Type -> begin
true
end
| _ -> begin
false
end))

let is_Kind = (fun _discr_ -> (match (_discr_) with
| Kind -> begin
true
end
| _ -> begin
false
end))

let is_Formula = (fun _discr_ -> (match (_discr_) with
| Formula -> begin
true
end
| _ -> begin
false
end))

type lid =
FStar_Absyn_Syntax.l__LongIdent

type imp =
| FsTypApp
| Hash
| Nothing

let is_FsTypApp = (fun _discr_ -> (match (_discr_) with
| FsTypApp -> begin
true
end
| _ -> begin
false
end))

let is_Hash = (fun _discr_ -> (match (_discr_) with
| Hash -> begin
true
end
| _ -> begin
false
end))

let is_Nothing = (fun _discr_ -> (match (_discr_) with
| Nothing -> begin
true
end
| _ -> begin
false
end))

type term' =
| Wild
| Const of FStar_Absyn_Syntax.sconst
| Op of (Prims.string * term Prims.list)
| Tvar of FStar_Absyn_Syntax.ident
| Var of lid
| Name of lid
| Construct of (lid * (term * imp) Prims.list)
| Abs of (pattern Prims.list * term)
| App of (term * term * imp)
| Let of (Prims.bool * (pattern * term) Prims.list * term)
| Seq of (term * term)
| If of (term * term * term)
| Match of (term * branch Prims.list)
| TryWith of (term * branch Prims.list)
| Ascribed of (term * term)
| Record of (term Prims.option * (lid * term) Prims.list)
| Project of (term * lid)
| Product of (binder Prims.list * term)
| Sum of (binder Prims.list * term)
| QForall of (binder Prims.list * term Prims.list Prims.list * term)
| QExists of (binder Prims.list * term Prims.list Prims.list * term)
| Refine of (binder * term)
| NamedTyp of (FStar_Absyn_Syntax.ident * term)
| Paren of term
| Requires of (term * Prims.string Prims.option)
| Ensures of (term * Prims.string Prims.option)
| Labeled of (term * Prims.string * Prims.bool) 
 and term =
{tm : term'; range : FStar_Range.range; level : level} 
 and binder' =
| Variable of FStar_Absyn_Syntax.ident
| TVariable of FStar_Absyn_Syntax.ident
| Annotated of (FStar_Absyn_Syntax.ident * term)
| TAnnotated of (FStar_Absyn_Syntax.ident * term)
| NoName of term 
 and binder =
{b : binder'; brange : FStar_Range.range; blevel : level; aqual : FStar_Absyn_Syntax.aqual} 
 and pattern' =
| PatWild
| PatConst of FStar_Absyn_Syntax.sconst
| PatApp of (pattern * pattern Prims.list)
| PatVar of (FStar_Absyn_Syntax.ident * Prims.bool)
| PatName of lid
| PatTvar of (FStar_Absyn_Syntax.ident * Prims.bool)
| PatList of pattern Prims.list
| PatTuple of (pattern Prims.list * Prims.bool)
| PatRecord of (lid * pattern) Prims.list
| PatAscribed of (pattern * term)
| PatOr of pattern Prims.list 
 and pattern =
{pat : pattern'; prange : FStar_Range.range} 
 and branch =
(pattern * term Prims.option * term)

let is_Wild = (fun _discr_ -> (match (_discr_) with
| Wild -> begin
true
end
| _ -> begin
false
end))

let is_Const = (fun _discr_ -> (match (_discr_) with
| Const (_) -> begin
true
end
| _ -> begin
false
end))

let is_Op = (fun _discr_ -> (match (_discr_) with
| Op (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tvar = (fun _discr_ -> (match (_discr_) with
| Tvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Var = (fun _discr_ -> (match (_discr_) with
| Var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Name = (fun _discr_ -> (match (_discr_) with
| Name (_) -> begin
true
end
| _ -> begin
false
end))

let is_Construct = (fun _discr_ -> (match (_discr_) with
| Construct (_) -> begin
true
end
| _ -> begin
false
end))

let is_Abs = (fun _discr_ -> (match (_discr_) with
| Abs (_) -> begin
true
end
| _ -> begin
false
end))

let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))

let is_Let = (fun _discr_ -> (match (_discr_) with
| Let (_) -> begin
true
end
| _ -> begin
false
end))

let is_Seq = (fun _discr_ -> (match (_discr_) with
| Seq (_) -> begin
true
end
| _ -> begin
false
end))

let is_If = (fun _discr_ -> (match (_discr_) with
| If (_) -> begin
true
end
| _ -> begin
false
end))

let is_Match = (fun _discr_ -> (match (_discr_) with
| Match (_) -> begin
true
end
| _ -> begin
false
end))

let is_TryWith = (fun _discr_ -> (match (_discr_) with
| TryWith (_) -> begin
true
end
| _ -> begin
false
end))

let is_Ascribed = (fun _discr_ -> (match (_discr_) with
| Ascribed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Record = (fun _discr_ -> (match (_discr_) with
| Record (_) -> begin
true
end
| _ -> begin
false
end))

let is_Project = (fun _discr_ -> (match (_discr_) with
| Project (_) -> begin
true
end
| _ -> begin
false
end))

let is_Product = (fun _discr_ -> (match (_discr_) with
| Product (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sum = (fun _discr_ -> (match (_discr_) with
| Sum (_) -> begin
true
end
| _ -> begin
false
end))

let is_QForall = (fun _discr_ -> (match (_discr_) with
| QForall (_) -> begin
true
end
| _ -> begin
false
end))

let is_QExists = (fun _discr_ -> (match (_discr_) with
| QExists (_) -> begin
true
end
| _ -> begin
false
end))

let is_Refine = (fun _discr_ -> (match (_discr_) with
| Refine (_) -> begin
true
end
| _ -> begin
false
end))

let is_NamedTyp = (fun _discr_ -> (match (_discr_) with
| NamedTyp (_) -> begin
true
end
| _ -> begin
false
end))

let is_Paren = (fun _discr_ -> (match (_discr_) with
| Paren (_) -> begin
true
end
| _ -> begin
false
end))

let is_Requires = (fun _discr_ -> (match (_discr_) with
| Requires (_) -> begin
true
end
| _ -> begin
false
end))

let is_Ensures = (fun _discr_ -> (match (_discr_) with
| Ensures (_) -> begin
true
end
| _ -> begin
false
end))

let is_Labeled = (fun _discr_ -> (match (_discr_) with
| Labeled (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkterm = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkterm"))))

let is_Variable = (fun _discr_ -> (match (_discr_) with
| Variable (_) -> begin
true
end
| _ -> begin
false
end))

let is_TVariable = (fun _discr_ -> (match (_discr_) with
| TVariable (_) -> begin
true
end
| _ -> begin
false
end))

let is_Annotated = (fun _discr_ -> (match (_discr_) with
| Annotated (_) -> begin
true
end
| _ -> begin
false
end))

let is_TAnnotated = (fun _discr_ -> (match (_discr_) with
| TAnnotated (_) -> begin
true
end
| _ -> begin
false
end))

let is_NoName = (fun _discr_ -> (match (_discr_) with
| NoName (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkbinder = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbinder"))))

let is_PatWild = (fun _discr_ -> (match (_discr_) with
| PatWild -> begin
true
end
| _ -> begin
false
end))

let is_PatConst = (fun _discr_ -> (match (_discr_) with
| PatConst (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatApp = (fun _discr_ -> (match (_discr_) with
| PatApp (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatVar = (fun _discr_ -> (match (_discr_) with
| PatVar (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatName = (fun _discr_ -> (match (_discr_) with
| PatName (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatTvar = (fun _discr_ -> (match (_discr_) with
| PatTvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatList = (fun _discr_ -> (match (_discr_) with
| PatList (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatTuple = (fun _discr_ -> (match (_discr_) with
| PatTuple (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatRecord = (fun _discr_ -> (match (_discr_) with
| PatRecord (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatAscribed = (fun _discr_ -> (match (_discr_) with
| PatAscribed (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatOr = (fun _discr_ -> (match (_discr_) with
| PatOr (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkpattern = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))

let ___Const____0 = (fun projectee -> (match (projectee) with
| Const (_40_13) -> begin
_40_13
end))

let ___Op____0 = (fun projectee -> (match (projectee) with
| Op (_40_16) -> begin
_40_16
end))

let ___Tvar____0 = (fun projectee -> (match (projectee) with
| Tvar (_40_19) -> begin
_40_19
end))

let ___Var____0 = (fun projectee -> (match (projectee) with
| Var (_40_22) -> begin
_40_22
end))

let ___Name____0 = (fun projectee -> (match (projectee) with
| Name (_40_25) -> begin
_40_25
end))

let ___Construct____0 = (fun projectee -> (match (projectee) with
| Construct (_40_28) -> begin
_40_28
end))

let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_40_31) -> begin
_40_31
end))

let ___App____0 = (fun projectee -> (match (projectee) with
| App (_40_34) -> begin
_40_34
end))

let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_40_37) -> begin
_40_37
end))

let ___Seq____0 = (fun projectee -> (match (projectee) with
| Seq (_40_40) -> begin
_40_40
end))

let ___If____0 = (fun projectee -> (match (projectee) with
| If (_40_43) -> begin
_40_43
end))

let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_40_46) -> begin
_40_46
end))

let ___TryWith____0 = (fun projectee -> (match (projectee) with
| TryWith (_40_49) -> begin
_40_49
end))

let ___Ascribed____0 = (fun projectee -> (match (projectee) with
| Ascribed (_40_52) -> begin
_40_52
end))

let ___Record____0 = (fun projectee -> (match (projectee) with
| Record (_40_55) -> begin
_40_55
end))

let ___Project____0 = (fun projectee -> (match (projectee) with
| Project (_40_58) -> begin
_40_58
end))

let ___Product____0 = (fun projectee -> (match (projectee) with
| Product (_40_61) -> begin
_40_61
end))

let ___Sum____0 = (fun projectee -> (match (projectee) with
| Sum (_40_64) -> begin
_40_64
end))

let ___QForall____0 = (fun projectee -> (match (projectee) with
| QForall (_40_67) -> begin
_40_67
end))

let ___QExists____0 = (fun projectee -> (match (projectee) with
| QExists (_40_70) -> begin
_40_70
end))

let ___Refine____0 = (fun projectee -> (match (projectee) with
| Refine (_40_73) -> begin
_40_73
end))

let ___NamedTyp____0 = (fun projectee -> (match (projectee) with
| NamedTyp (_40_76) -> begin
_40_76
end))

let ___Paren____0 = (fun projectee -> (match (projectee) with
| Paren (_40_79) -> begin
_40_79
end))

let ___Requires____0 = (fun projectee -> (match (projectee) with
| Requires (_40_82) -> begin
_40_82
end))

let ___Ensures____0 = (fun projectee -> (match (projectee) with
| Ensures (_40_85) -> begin
_40_85
end))

let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_40_88) -> begin
_40_88
end))

let ___Variable____0 = (fun projectee -> (match (projectee) with
| Variable (_40_92) -> begin
_40_92
end))

let ___TVariable____0 = (fun projectee -> (match (projectee) with
| TVariable (_40_95) -> begin
_40_95
end))

let ___Annotated____0 = (fun projectee -> (match (projectee) with
| Annotated (_40_98) -> begin
_40_98
end))

let ___TAnnotated____0 = (fun projectee -> (match (projectee) with
| TAnnotated (_40_101) -> begin
_40_101
end))

let ___NoName____0 = (fun projectee -> (match (projectee) with
| NoName (_40_104) -> begin
_40_104
end))

let ___PatConst____0 = (fun projectee -> (match (projectee) with
| PatConst (_40_108) -> begin
_40_108
end))

let ___PatApp____0 = (fun projectee -> (match (projectee) with
| PatApp (_40_111) -> begin
_40_111
end))

let ___PatVar____0 = (fun projectee -> (match (projectee) with
| PatVar (_40_114) -> begin
_40_114
end))

let ___PatName____0 = (fun projectee -> (match (projectee) with
| PatName (_40_117) -> begin
_40_117
end))

let ___PatTvar____0 = (fun projectee -> (match (projectee) with
| PatTvar (_40_120) -> begin
_40_120
end))

let ___PatList____0 = (fun projectee -> (match (projectee) with
| PatList (_40_123) -> begin
_40_123
end))

let ___PatTuple____0 = (fun projectee -> (match (projectee) with
| PatTuple (_40_126) -> begin
_40_126
end))

let ___PatRecord____0 = (fun projectee -> (match (projectee) with
| PatRecord (_40_129) -> begin
_40_129
end))

let ___PatAscribed____0 = (fun projectee -> (match (projectee) with
| PatAscribed (_40_132) -> begin
_40_132
end))

let ___PatOr____0 = (fun projectee -> (match (projectee) with
| PatOr (_40_135) -> begin
_40_135
end))

type knd =
term

type typ =
term

type expr =
term

type tycon =
| TyconAbstract of (FStar_Absyn_Syntax.ident * binder Prims.list * knd Prims.option)
| TyconAbbrev of (FStar_Absyn_Syntax.ident * binder Prims.list * knd Prims.option * term)
| TyconRecord of (FStar_Absyn_Syntax.ident * binder Prims.list * knd Prims.option * (FStar_Absyn_Syntax.ident * term) Prims.list)
| TyconVariant of (FStar_Absyn_Syntax.ident * binder Prims.list * knd Prims.option * (FStar_Absyn_Syntax.ident * term Prims.option * Prims.bool) Prims.list)

let is_TyconAbstract = (fun _discr_ -> (match (_discr_) with
| TyconAbstract (_) -> begin
true
end
| _ -> begin
false
end))

let is_TyconAbbrev = (fun _discr_ -> (match (_discr_) with
| TyconAbbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_TyconRecord = (fun _discr_ -> (match (_discr_) with
| TyconRecord (_) -> begin
true
end
| _ -> begin
false
end))

let is_TyconVariant = (fun _discr_ -> (match (_discr_) with
| TyconVariant (_) -> begin
true
end
| _ -> begin
false
end))

let ___TyconAbstract____0 = (fun projectee -> (match (projectee) with
| TyconAbstract (_40_139) -> begin
_40_139
end))

let ___TyconAbbrev____0 = (fun projectee -> (match (projectee) with
| TyconAbbrev (_40_142) -> begin
_40_142
end))

let ___TyconRecord____0 = (fun projectee -> (match (projectee) with
| TyconRecord (_40_145) -> begin
_40_145
end))

let ___TyconVariant____0 = (fun projectee -> (match (projectee) with
| TyconVariant (_40_148) -> begin
_40_148
end))

type qualifiers =
FStar_Absyn_Syntax.qualifier Prims.list

type lift =
{msource : lid; mdest : lid; lift_op : term}

let is_Mklift = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklift"))))

type decl' =
| Open of lid
| KindAbbrev of (FStar_Absyn_Syntax.ident * binder Prims.list * knd)
| ToplevelLet of (Prims.bool * (pattern * term) Prims.list)
| Main of term
| Assume of (qualifiers * FStar_Absyn_Syntax.ident * term)
| Tycon of (qualifiers * tycon Prims.list)
| Val of (qualifiers * FStar_Absyn_Syntax.ident * term)
| Exception of (FStar_Absyn_Syntax.ident * term Prims.option)
| NewEffect of (qualifiers * effect_decl)
| SubEffect of lift
| Pragma of FStar_Absyn_Syntax.pragma 
 and decl =
{d : decl'; drange : FStar_Range.range} 
 and effect_decl =
| DefineEffect of (FStar_Absyn_Syntax.ident * binder Prims.list * term * decl Prims.list)
| RedefineEffect of (FStar_Absyn_Syntax.ident * binder Prims.list * term)

let is_Open = (fun _discr_ -> (match (_discr_) with
| Open (_) -> begin
true
end
| _ -> begin
false
end))

let is_KindAbbrev = (fun _discr_ -> (match (_discr_) with
| KindAbbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_ToplevelLet = (fun _discr_ -> (match (_discr_) with
| ToplevelLet (_) -> begin
true
end
| _ -> begin
false
end))

let is_Main = (fun _discr_ -> (match (_discr_) with
| Main (_) -> begin
true
end
| _ -> begin
false
end))

let is_Assume = (fun _discr_ -> (match (_discr_) with
| Assume (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tycon = (fun _discr_ -> (match (_discr_) with
| Tycon (_) -> begin
true
end
| _ -> begin
false
end))

let is_Val = (fun _discr_ -> (match (_discr_) with
| Val (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exception = (fun _discr_ -> (match (_discr_) with
| Exception (_) -> begin
true
end
| _ -> begin
false
end))

let is_NewEffect = (fun _discr_ -> (match (_discr_) with
| NewEffect (_) -> begin
true
end
| _ -> begin
false
end))

let is_SubEffect = (fun _discr_ -> (match (_discr_) with
| SubEffect (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pragma = (fun _discr_ -> (match (_discr_) with
| Pragma (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkdecl = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdecl"))))

let is_DefineEffect = (fun _discr_ -> (match (_discr_) with
| DefineEffect (_) -> begin
true
end
| _ -> begin
false
end))

let is_RedefineEffect = (fun _discr_ -> (match (_discr_) with
| RedefineEffect (_) -> begin
true
end
| _ -> begin
false
end))

let ___Open____0 = (fun projectee -> (match (projectee) with
| Open (_40_157) -> begin
_40_157
end))

let ___KindAbbrev____0 = (fun projectee -> (match (projectee) with
| KindAbbrev (_40_160) -> begin
_40_160
end))

let ___ToplevelLet____0 = (fun projectee -> (match (projectee) with
| ToplevelLet (_40_163) -> begin
_40_163
end))

let ___Main____0 = (fun projectee -> (match (projectee) with
| Main (_40_166) -> begin
_40_166
end))

let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_40_169) -> begin
_40_169
end))

let ___Tycon____0 = (fun projectee -> (match (projectee) with
| Tycon (_40_172) -> begin
_40_172
end))

let ___Val____0 = (fun projectee -> (match (projectee) with
| Val (_40_175) -> begin
_40_175
end))

let ___Exception____0 = (fun projectee -> (match (projectee) with
| Exception (_40_178) -> begin
_40_178
end))

let ___NewEffect____0 = (fun projectee -> (match (projectee) with
| NewEffect (_40_181) -> begin
_40_181
end))

let ___SubEffect____0 = (fun projectee -> (match (projectee) with
| SubEffect (_40_184) -> begin
_40_184
end))

let ___Pragma____0 = (fun projectee -> (match (projectee) with
| Pragma (_40_187) -> begin
_40_187
end))

let ___DefineEffect____0 = (fun projectee -> (match (projectee) with
| DefineEffect (_40_191) -> begin
_40_191
end))

let ___RedefineEffect____0 = (fun projectee -> (match (projectee) with
| RedefineEffect (_40_194) -> begin
_40_194
end))

type modul =
| Module of (FStar_Absyn_Syntax.l__LongIdent * decl Prims.list)
| Interface of (FStar_Absyn_Syntax.l__LongIdent * decl Prims.list * Prims.bool)

let is_Module = (fun _discr_ -> (match (_discr_) with
| Module (_) -> begin
true
end
| _ -> begin
false
end))

let is_Interface = (fun _discr_ -> (match (_discr_) with
| Interface (_) -> begin
true
end
| _ -> begin
false
end))

let ___Module____0 = (fun projectee -> (match (projectee) with
| Module (_40_197) -> begin
_40_197
end))

let ___Interface____0 = (fun projectee -> (match (projectee) with
| Interface (_40_200) -> begin
_40_200
end))

type file =
modul Prims.list

type inputFragment =
(file, decl Prims.list) FStar_Util.either

let mk_decl = (fun d r -> {d = d; drange = r})

let mk_binder = (fun b r l i -> {b = b; brange = r; blevel = l; aqual = i})

let mk_term = (fun t r l -> {tm = t; range = r; level = l})

let mk_pattern = (fun p r -> {pat = p; prange = r})

let un_curry_abs = (fun ps body -> (match (body.tm) with
| Abs (p', body') -> begin
Abs (((FStar_List.append ps p'), body'))
end
| _40_219 -> begin
Abs ((ps, body))
end))

let mk_function = (fun branches r1 r2 -> (let x = (FStar_Absyn_Util.genident (Some (r1)))
in (let _106_937 = (let _106_936 = (let _106_935 = (let _106_934 = (let _106_933 = (let _106_932 = (let _106_931 = (let _106_930 = (FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in Var (_106_930))
in (mk_term _106_931 r1 Expr))
in (_106_932, branches))
in Match (_106_933))
in (mk_term _106_934 r2 Expr))
in (((mk_pattern (PatVar ((x, false))) r1))::[], _106_935))
in Abs (_106_936))
in (mk_term _106_937 r2 Expr))))

let un_function = (fun p tm -> (match ((p.pat, tm.tm)) with
| (PatVar (_40_227), Abs (pats, body)) -> begin
Some (((mk_pattern (PatApp ((p, pats))) p.prange), body))
end
| _40_235 -> begin
None
end))

let lid_with_range = (fun lid r -> (let _106_946 = (FStar_Absyn_Syntax.path_of_lid lid)
in (FStar_Absyn_Syntax.lid_of_path _106_946 r)))

let to_string_l = (fun sep f l -> (let _106_953 = (FStar_List.map f l)
in (FStar_String.concat sep _106_953)))

let imp_to_string = (fun _40_1 -> (match (_40_1) with
| Hash -> begin
"#"
end
| _40_244 -> begin
""
end))

let rec term_to_string = (fun x -> (match (x.tm) with
| Wild -> begin
"_"
end
| Requires (t, _40_249) -> begin
(let _106_960 = (term_to_string t)
in (FStar_Util.format1 "(requires %s)" _106_960))
end
| Ensures (t, _40_254) -> begin
(let _106_961 = (term_to_string t)
in (FStar_Util.format1 "(ensures %s)" _106_961))
end
| Labeled (t, l, _40_260) -> begin
(let _106_962 = (term_to_string t)
in (FStar_Util.format2 "(labeled %s %s)" l _106_962))
end
| Const (c) -> begin
(FStar_Absyn_Print.const_to_string c)
end
| Op (s, xs) -> begin
(let _106_965 = (let _106_964 = (FStar_List.map (fun x -> (FStar_All.pipe_right x term_to_string)) xs)
in (FStar_String.concat ", " _106_964))
in (FStar_Util.format2 "%s(%s)" s _106_965))
end
| Tvar (id) -> begin
id.FStar_Absyn_Syntax.idText
end
| (Var (l)) | (Name (l)) -> begin
(FStar_Absyn_Print.sli l)
end
| Construct (l, args) -> begin
(let _106_969 = (FStar_Absyn_Print.sli l)
in (let _106_968 = (to_string_l " " (fun _40_281 -> (match (_40_281) with
| (a, imp) -> begin
(let _106_967 = (term_to_string a)
in (FStar_Util.format2 "%s%s" (imp_to_string imp) _106_967))
end)) args)
in (FStar_Util.format2 "(%s %s)" _106_969 _106_968)))
end
| Abs (pats, t) when (x.level = Expr) -> begin
(let _106_971 = (to_string_l " " pat_to_string pats)
in (let _106_970 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _106_971 _106_970)))
end
| Abs (pats, t) when (x.level = Type) -> begin
(let _106_973 = (to_string_l " " pat_to_string pats)
in (let _106_972 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s => %s)" _106_973 _106_972)))
end
| App (t1, t2, imp) -> begin
(let _106_975 = (FStar_All.pipe_right t1 term_to_string)
in (let _106_974 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format3 "%s %s%s" _106_975 (imp_to_string imp) _106_974)))
end
| Let (false, (pat, tm)::[], body) -> begin
(let _106_978 = (FStar_All.pipe_right pat pat_to_string)
in (let _106_977 = (FStar_All.pipe_right tm term_to_string)
in (let _106_976 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format3 "let %s = %s in %s" _106_978 _106_977 _106_976))))
end
| Let (_40_304, lbs, body) -> begin
(let _106_983 = (to_string_l " and " (fun _40_311 -> (match (_40_311) with
| (p, b) -> begin
(let _106_981 = (FStar_All.pipe_right p pat_to_string)
in (let _106_980 = (FStar_All.pipe_right b term_to_string)
in (FStar_Util.format2 "%s=%s" _106_981 _106_980)))
end)) lbs)
in (let _106_982 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format2 "let rec %s in %s" _106_983 _106_982)))
end
| Seq (t1, t2) -> begin
(let _106_985 = (FStar_All.pipe_right t1 term_to_string)
in (let _106_984 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "%s; %s" _106_985 _106_984)))
end
| If (t1, t2, t3) -> begin
(let _106_988 = (FStar_All.pipe_right t1 term_to_string)
in (let _106_987 = (FStar_All.pipe_right t2 term_to_string)
in (let _106_986 = (FStar_All.pipe_right t3 term_to_string)
in (FStar_Util.format3 "if %s then %s else %s" _106_988 _106_987 _106_986))))
end
| Match (t, branches) -> begin
(let _106_995 = (FStar_All.pipe_right t term_to_string)
in (let _106_994 = (to_string_l " | " (fun _40_328 -> (match (_40_328) with
| (p, w, e) -> begin
(let _106_993 = (FStar_All.pipe_right p pat_to_string)
in (let _106_992 = (match (w) with
| None -> begin
""
end
| Some (e) -> begin
(let _106_990 = (term_to_string e)
in (FStar_Util.format1 "when %s" _106_990))
end)
in (let _106_991 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _106_993 _106_992 _106_991))))
end)) branches)
in (FStar_Util.format2 "match %s with %s" _106_995 _106_994)))
end
| Ascribed (t1, t2) -> begin
(let _106_997 = (FStar_All.pipe_right t1 term_to_string)
in (let _106_996 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "(%s : %s)" _106_997 _106_996)))
end
| Record (Some (e), fields) -> begin
(let _106_1002 = (FStar_All.pipe_right e term_to_string)
in (let _106_1001 = (to_string_l " " (fun _40_343 -> (match (_40_343) with
| (l, e) -> begin
(let _106_1000 = (FStar_Absyn_Print.sli l)
in (let _106_999 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" _106_1000 _106_999)))
end)) fields)
in (FStar_Util.format2 "{%s with %s}" _106_1002 _106_1001)))
end
| Record (None, fields) -> begin
(let _106_1006 = (to_string_l " " (fun _40_350 -> (match (_40_350) with
| (l, e) -> begin
(let _106_1005 = (FStar_Absyn_Print.sli l)
in (let _106_1004 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" _106_1005 _106_1004)))
end)) fields)
in (FStar_Util.format1 "{%s}" _106_1006))
end
| Project (e, l) -> begin
(let _106_1008 = (FStar_All.pipe_right e term_to_string)
in (let _106_1007 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format2 "%s.%s" _106_1008 _106_1007)))
end
| Product ([], t) -> begin
(term_to_string t)
end
| Product (b::hd::tl, t) -> begin
(term_to_string (mk_term (Product (((b)::[], (mk_term (Product (((hd)::tl, t))) x.range x.level)))) x.range x.level))
end
| Product (b::[], t) when (x.level = Type) -> begin
(let _106_1010 = (FStar_All.pipe_right b binder_to_string)
in (let _106_1009 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s -> %s" _106_1010 _106_1009)))
end
| Product (b::[], t) when (x.level = Kind) -> begin
(let _106_1012 = (FStar_All.pipe_right b binder_to_string)
in (let _106_1011 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s => %s" _106_1012 _106_1011)))
end
| Sum (binders, t) -> begin
(let _106_1015 = (let _106_1013 = (FStar_All.pipe_right binders (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _106_1013 (FStar_String.concat " * ")))
in (let _106_1014 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s * %s" _106_1015 _106_1014)))
end
| QForall (bs, pats, t) -> begin
(let _106_1018 = (to_string_l " " binder_to_string bs)
in (let _106_1017 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _106_1016 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "forall %s.{:pattern %s} %s" _106_1018 _106_1017 _106_1016))))
end
| QExists (bs, pats, t) -> begin
(let _106_1021 = (to_string_l " " binder_to_string bs)
in (let _106_1020 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _106_1019 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "exists %s.{:pattern %s} %s" _106_1021 _106_1020 _106_1019))))
end
| Refine (b, t) -> begin
(let _106_1023 = (FStar_All.pipe_right b binder_to_string)
in (let _106_1022 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:{%s}" _106_1023 _106_1022)))
end
| NamedTyp (x, t) -> begin
(let _106_1024 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" x.FStar_Absyn_Syntax.idText _106_1024))
end
| Paren (t) -> begin
(let _106_1025 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format1 "(%s)" _106_1025))
end
| Product (bs, t) -> begin
(let _106_1028 = (let _106_1026 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _106_1026 (FStar_String.concat ",")))
in (let _106_1027 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "Unidentified product: [%s] %s" _106_1028 _106_1027)))
end
| t -> begin
(FStar_All.failwith "Missing case in term_to_string")
end))
and binder_to_string = (fun x -> (let s = (match (x.b) with
| Variable (i) -> begin
i.FStar_Absyn_Syntax.idText
end
| TVariable (i) -> begin
(FStar_Util.format1 "%s:_" i.FStar_Absyn_Syntax.idText)
end
| (TAnnotated (i, t)) | (Annotated (i, t)) -> begin
(let _106_1030 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Absyn_Syntax.idText _106_1030))
end
| NoName (t) -> begin
(FStar_All.pipe_right t term_to_string)
end)
in (match (x.aqual) with
| Some (FStar_Absyn_Syntax.Implicit) -> begin
(FStar_Util.format1 "#%s" s)
end
| Some (FStar_Absyn_Syntax.Equality) -> begin
(FStar_Util.format1 "=%s" s)
end
| _40_425 -> begin
s
end)))
and pat_to_string = (fun x -> (match (x.pat) with
| PatWild -> begin
"_"
end
| PatConst (c) -> begin
(FStar_Absyn_Print.const_to_string c)
end
| PatApp (p, ps) -> begin
(let _106_1033 = (FStar_All.pipe_right p pat_to_string)
in (let _106_1032 = (to_string_l " " pat_to_string ps)
in (FStar_Util.format2 "(%s %s)" _106_1033 _106_1032)))
end
| (PatTvar (i, true)) | (PatVar (i, true)) -> begin
(FStar_Util.format1 "#%s" i.FStar_Absyn_Syntax.idText)
end
| (PatTvar (i, false)) | (PatVar (i, false)) -> begin
i.FStar_Absyn_Syntax.idText
end
| PatName (l) -> begin
(FStar_Absyn_Print.sli l)
end
| PatList (l) -> begin
(let _106_1034 = (to_string_l "; " pat_to_string l)
in (FStar_Util.format1 "[%s]" _106_1034))
end
| PatTuple (l, false) -> begin
(let _106_1035 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(%s)" _106_1035))
end
| PatTuple (l, true) -> begin
(let _106_1036 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(|%s|)" _106_1036))
end
| PatRecord (l) -> begin
(let _106_1040 = (to_string_l "; " (fun _40_464 -> (match (_40_464) with
| (f, e) -> begin
(let _106_1039 = (FStar_Absyn_Print.sli f)
in (let _106_1038 = (FStar_All.pipe_right e pat_to_string)
in (FStar_Util.format2 "%s=%s" _106_1039 _106_1038)))
end)) l)
in (FStar_Util.format1 "{%s}" _106_1040))
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatAscribed (p, t) -> begin
(let _106_1042 = (FStar_All.pipe_right p pat_to_string)
in (let _106_1041 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(%s:%s)" _106_1042 _106_1041)))
end))

let error = (fun msg tm r -> (let tm = (FStar_All.pipe_right tm term_to_string)
in (let tm = if ((FStar_String.length tm) >= 80) then begin
(let _106_1046 = (FStar_Util.substring tm 0 77)
in (Prims.strcat _106_1046 "..."))
end else begin
tm
end
in (Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat msg "\n") tm), r)))))))

let consPat = (fun r hd tl -> PatApp (((mk_pattern (PatName (FStar_Absyn_Const.cons_lid)) r), (hd)::(tl)::[])))

let consTerm = (fun r hd tl -> (mk_term (Construct ((FStar_Absyn_Const.cons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))

let lexConsTerm = (fun r hd tl -> (mk_term (Construct ((FStar_Absyn_Const.lexcons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))

let mkConsList = (fun r elts -> (let nil = (mk_term (Construct ((FStar_Absyn_Const.nil_lid, []))) r Expr)
in (FStar_List.fold_right (fun e tl -> (consTerm r e tl)) elts nil)))

let mkLexList = (fun r elts -> (let nil = (mk_term (Construct ((FStar_Absyn_Const.lextop_lid, []))) r Expr)
in (FStar_List.fold_right (fun e tl -> (lexConsTerm r e tl)) elts nil)))

let mkApp = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _40_500 -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct ((s, args))) r Un)
end
| _40_504 -> begin
(FStar_List.fold_left (fun t _40_508 -> (match (_40_508) with
| (a, imp) -> begin
(mk_term (App ((t, a, imp))) r Un)
end)) t args)
end)
end))

let mkRefSet = (fun r elts -> (let empty = (let _106_1090 = (let _106_1089 = (FStar_Absyn_Util.set_lid_range FStar_Absyn_Const.set_empty r)
in Var (_106_1089))
in (mk_term _106_1090 r Expr))
in (let ref_constr = (let _106_1092 = (let _106_1091 = (FStar_Absyn_Util.set_lid_range FStar_Absyn_Const.heap_ref r)
in Var (_106_1091))
in (mk_term _106_1092 r Expr))
in (let singleton = (let _106_1094 = (let _106_1093 = (FStar_Absyn_Util.set_lid_range FStar_Absyn_Const.set_singleton r)
in Var (_106_1093))
in (mk_term _106_1094 r Expr))
in (let union = (let _106_1096 = (let _106_1095 = (FStar_Absyn_Util.set_lid_range FStar_Absyn_Const.set_union r)
in Var (_106_1095))
in (mk_term _106_1096 r Expr))
in (FStar_List.fold_right (fun e tl -> (let e = (mkApp ref_constr (((e, Nothing))::[]) r)
in (let single_e = (mkApp singleton (((e, Nothing))::[]) r)
in (mkApp union (((single_e, Nothing))::((tl, Nothing))::[]) r)))) elts empty))))))

let mkExplicitApp = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _40_524 -> begin
(match (t.tm) with
| Name (s) -> begin
(let _106_1108 = (let _106_1107 = (let _106_1106 = (FStar_List.map (fun a -> (a, Nothing)) args)
in (s, _106_1106))
in Construct (_106_1107))
in (mk_term _106_1108 r Un))
end
| _40_529 -> begin
(FStar_List.fold_left (fun t a -> (mk_term (App ((t, a, Nothing))) r Un)) t args)
end)
end))

let mkAdmitMagic = (fun r -> (let unit_const = (mk_term (Const (FStar_Absyn_Syntax.Const_unit)) r Expr)
in (let admit = (let admit_name = (let _106_1114 = (let _106_1113 = (FStar_Absyn_Util.set_lid_range FStar_Absyn_Const.admit_lid r)
in Var (_106_1113))
in (mk_term _106_1114 r Expr))
in (mkExplicitApp admit_name ((unit_const)::[]) r))
in (let magic = (let magic_name = (let _106_1116 = (let _106_1115 = (FStar_Absyn_Util.set_lid_range FStar_Absyn_Const.magic_lid r)
in Var (_106_1115))
in (mk_term _106_1116 r Expr))
in (mkExplicitApp magic_name ((unit_const)::[]) r))
in (let admit_magic = (mk_term (Seq ((admit, magic))) r Expr)
in admit_magic)))))

let mkWildAdmitMagic = (fun r -> (let _106_1118 = (mkAdmitMagic r)
in ((mk_pattern PatWild r), None, _106_1118)))

let focusBranches = (fun branches r -> (let should_filter = (FStar_Util.for_some Prims.fst branches)
in if should_filter then begin
(let _40_543 = (FStar_Tc_Errors.warn r "Focusing on only some cases")
in (let focussed = (let _106_1121 = (FStar_List.filter Prims.fst branches)
in (FStar_All.pipe_right _106_1121 (FStar_List.map Prims.snd)))
in (let _106_1123 = (let _106_1122 = (mkWildAdmitMagic r)
in (_106_1122)::[])
in (FStar_List.append focussed _106_1123))))
end else begin
(FStar_All.pipe_right branches (FStar_List.map Prims.snd))
end))

let focusLetBindings = (fun lbs r -> (let should_filter = (FStar_Util.for_some Prims.fst lbs)
in if should_filter then begin
(let _40_549 = (FStar_Tc_Errors.warn r "Focusing on only some cases in this (mutually) recursive definition")
in (FStar_List.map (fun _40_553 -> (match (_40_553) with
| (f, lb) -> begin
if f then begin
lb
end else begin
(let _106_1127 = (mkAdmitMagic r)
in ((Prims.fst lb), _106_1127))
end
end)) lbs))
end else begin
(FStar_All.pipe_right lbs (FStar_List.map Prims.snd))
end))

let mkFsTypApp = (fun t args r -> (let _106_1135 = (FStar_List.map (fun a -> (a, FsTypApp)) args)
in (mkApp t _106_1135 r)))

let mkTuple = (fun args r -> (let cons = (FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) r)
in (let _106_1141 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _106_1141 r))))

let mkDTuple = (fun args r -> (let cons = (FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) r)
in (let _106_1147 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _106_1147 r))))

let mkRefinedBinder = (fun id t refopt m implicit -> (let b = (mk_binder (Annotated ((id, t))) m Type implicit)
in (match (refopt) with
| None -> begin
b
end
| Some (t) -> begin
(mk_binder (Annotated ((id, (mk_term (Refine ((b, t))) m Type)))) m Type implicit)
end)))

let rec extract_named_refinement = (fun t1 -> (match (t1.tm) with
| NamedTyp (x, t) -> begin
Some ((x, t, None))
end
| Refine ({b = Annotated (x, t); brange = _40_585; blevel = _40_583; aqual = _40_581}, t') -> begin
Some ((x, t, Some (t')))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| _40_597 -> begin
None
end))




