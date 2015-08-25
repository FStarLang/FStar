
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
Microsoft_FStar_Absyn_Syntax.l__LongIdent

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
| Const of Microsoft_FStar_Absyn_Syntax.sconst
| Op of (Prims.string * term Prims.list)
| Tvar of Microsoft_FStar_Absyn_Syntax.ident
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
| QForall of (binder Prims.list * term Prims.list * term)
| QExists of (binder Prims.list * term Prims.list * term)
| Refine of (binder * term)
| NamedTyp of (Microsoft_FStar_Absyn_Syntax.ident * term)
| Paren of term
| Requires of (term * Prims.string Prims.option)
| Ensures of (term * Prims.string Prims.option)
| Labeled of (term * Prims.string * Prims.bool) 
 and term =
{tm : term'; range : Microsoft_FStar_Range.range; level : level} 
 and binder' =
| Variable of Microsoft_FStar_Absyn_Syntax.ident
| TVariable of Microsoft_FStar_Absyn_Syntax.ident
| Annotated of (Microsoft_FStar_Absyn_Syntax.ident * term)
| TAnnotated of (Microsoft_FStar_Absyn_Syntax.ident * term)
| NoName of term 
 and binder =
{b : binder'; brange : Microsoft_FStar_Range.range; blevel : level; aqual : Microsoft_FStar_Absyn_Syntax.aqual} 
 and pattern' =
| PatWild
| PatConst of Microsoft_FStar_Absyn_Syntax.sconst
| PatApp of (pattern * pattern Prims.list)
| PatVar of (Microsoft_FStar_Absyn_Syntax.ident * Prims.bool)
| PatName of lid
| PatTvar of (Microsoft_FStar_Absyn_Syntax.ident * Prims.bool)
| PatList of pattern Prims.list
| PatTuple of (pattern Prims.list * Prims.bool)
| PatRecord of (lid * pattern) Prims.list
| PatAscribed of (pattern * term)
| PatOr of pattern Prims.list 
 and pattern =
{pat : pattern'; prange : Microsoft_FStar_Range.range} 
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

let is_Mkterm = (fun _ -> (All.failwith "Not yet implemented:is_Mkterm"))

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

let is_Mkbinder = (fun _ -> (All.failwith "Not yet implemented:is_Mkbinder"))

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

let is_Mkpattern = (fun _ -> (All.failwith "Not yet implemented:is_Mkpattern"))

let ___Const____0 = (fun projectee -> (match (projectee) with
| Const (_39_13) -> begin
_39_13
end))

let ___Op____0 = (fun projectee -> (match (projectee) with
| Op (_39_16) -> begin
_39_16
end))

let ___Tvar____0 = (fun projectee -> (match (projectee) with
| Tvar (_39_19) -> begin
_39_19
end))

let ___Var____0 = (fun projectee -> (match (projectee) with
| Var (_39_22) -> begin
_39_22
end))

let ___Name____0 = (fun projectee -> (match (projectee) with
| Name (_39_25) -> begin
_39_25
end))

let ___Construct____0 = (fun projectee -> (match (projectee) with
| Construct (_39_28) -> begin
_39_28
end))

let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_39_31) -> begin
_39_31
end))

let ___App____0 = (fun projectee -> (match (projectee) with
| App (_39_34) -> begin
_39_34
end))

let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_39_37) -> begin
_39_37
end))

let ___Seq____0 = (fun projectee -> (match (projectee) with
| Seq (_39_40) -> begin
_39_40
end))

let ___If____0 = (fun projectee -> (match (projectee) with
| If (_39_43) -> begin
_39_43
end))

let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_39_46) -> begin
_39_46
end))

let ___TryWith____0 = (fun projectee -> (match (projectee) with
| TryWith (_39_49) -> begin
_39_49
end))

let ___Ascribed____0 = (fun projectee -> (match (projectee) with
| Ascribed (_39_52) -> begin
_39_52
end))

let ___Record____0 = (fun projectee -> (match (projectee) with
| Record (_39_55) -> begin
_39_55
end))

let ___Project____0 = (fun projectee -> (match (projectee) with
| Project (_39_58) -> begin
_39_58
end))

let ___Product____0 = (fun projectee -> (match (projectee) with
| Product (_39_61) -> begin
_39_61
end))

let ___Sum____0 = (fun projectee -> (match (projectee) with
| Sum (_39_64) -> begin
_39_64
end))

let ___QForall____0 = (fun projectee -> (match (projectee) with
| QForall (_39_67) -> begin
_39_67
end))

let ___QExists____0 = (fun projectee -> (match (projectee) with
| QExists (_39_70) -> begin
_39_70
end))

let ___Refine____0 = (fun projectee -> (match (projectee) with
| Refine (_39_73) -> begin
_39_73
end))

let ___NamedTyp____0 = (fun projectee -> (match (projectee) with
| NamedTyp (_39_76) -> begin
_39_76
end))

let ___Paren____0 = (fun projectee -> (match (projectee) with
| Paren (_39_79) -> begin
_39_79
end))

let ___Requires____0 = (fun projectee -> (match (projectee) with
| Requires (_39_82) -> begin
_39_82
end))

let ___Ensures____0 = (fun projectee -> (match (projectee) with
| Ensures (_39_85) -> begin
_39_85
end))

let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_39_88) -> begin
_39_88
end))

let ___Variable____0 = (fun projectee -> (match (projectee) with
| Variable (_39_92) -> begin
_39_92
end))

let ___TVariable____0 = (fun projectee -> (match (projectee) with
| TVariable (_39_95) -> begin
_39_95
end))

let ___Annotated____0 = (fun projectee -> (match (projectee) with
| Annotated (_39_98) -> begin
_39_98
end))

let ___TAnnotated____0 = (fun projectee -> (match (projectee) with
| TAnnotated (_39_101) -> begin
_39_101
end))

let ___NoName____0 = (fun projectee -> (match (projectee) with
| NoName (_39_104) -> begin
_39_104
end))

let ___PatConst____0 = (fun projectee -> (match (projectee) with
| PatConst (_39_108) -> begin
_39_108
end))

let ___PatApp____0 = (fun projectee -> (match (projectee) with
| PatApp (_39_111) -> begin
_39_111
end))

let ___PatVar____0 = (fun projectee -> (match (projectee) with
| PatVar (_39_114) -> begin
_39_114
end))

let ___PatName____0 = (fun projectee -> (match (projectee) with
| PatName (_39_117) -> begin
_39_117
end))

let ___PatTvar____0 = (fun projectee -> (match (projectee) with
| PatTvar (_39_120) -> begin
_39_120
end))

let ___PatList____0 = (fun projectee -> (match (projectee) with
| PatList (_39_123) -> begin
_39_123
end))

let ___PatTuple____0 = (fun projectee -> (match (projectee) with
| PatTuple (_39_126) -> begin
_39_126
end))

let ___PatRecord____0 = (fun projectee -> (match (projectee) with
| PatRecord (_39_129) -> begin
_39_129
end))

let ___PatAscribed____0 = (fun projectee -> (match (projectee) with
| PatAscribed (_39_132) -> begin
_39_132
end))

let ___PatOr____0 = (fun projectee -> (match (projectee) with
| PatOr (_39_135) -> begin
_39_135
end))

type knd =
term

type typ =
term

type expr =
term

type tycon =
| TyconAbstract of (Microsoft_FStar_Absyn_Syntax.ident * binder Prims.list * knd Prims.option)
| TyconAbbrev of (Microsoft_FStar_Absyn_Syntax.ident * binder Prims.list * knd Prims.option * term)
| TyconRecord of (Microsoft_FStar_Absyn_Syntax.ident * binder Prims.list * knd Prims.option * (Microsoft_FStar_Absyn_Syntax.ident * term) Prims.list)
| TyconVariant of (Microsoft_FStar_Absyn_Syntax.ident * binder Prims.list * knd Prims.option * (Microsoft_FStar_Absyn_Syntax.ident * term Prims.option * Prims.bool) Prims.list)

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
| TyconAbstract (_39_139) -> begin
_39_139
end))

let ___TyconAbbrev____0 = (fun projectee -> (match (projectee) with
| TyconAbbrev (_39_142) -> begin
_39_142
end))

let ___TyconRecord____0 = (fun projectee -> (match (projectee) with
| TyconRecord (_39_145) -> begin
_39_145
end))

let ___TyconVariant____0 = (fun projectee -> (match (projectee) with
| TyconVariant (_39_148) -> begin
_39_148
end))

type qualifiers =
Microsoft_FStar_Absyn_Syntax.qualifier Prims.list

type lift =
{msource : lid; mdest : lid; lift_op : term}

let is_Mklift = (fun _ -> (All.failwith "Not yet implemented:is_Mklift"))

type decl' =
| Open of lid
| KindAbbrev of (Microsoft_FStar_Absyn_Syntax.ident * binder Prims.list * knd)
| ToplevelLet of (Prims.bool * (pattern * term) Prims.list)
| Main of term
| Assume of (qualifiers * Microsoft_FStar_Absyn_Syntax.ident * term)
| Tycon of (qualifiers * tycon Prims.list)
| Val of (qualifiers * Microsoft_FStar_Absyn_Syntax.ident * term)
| Exception of (Microsoft_FStar_Absyn_Syntax.ident * term Prims.option)
| NewEffect of (qualifiers * effect_decl)
| SubEffect of lift
| Pragma of Microsoft_FStar_Absyn_Syntax.pragma 
 and decl =
{d : decl'; drange : Microsoft_FStar_Range.range} 
 and effect_decl =
| DefineEffect of (Microsoft_FStar_Absyn_Syntax.ident * binder Prims.list * term * decl Prims.list)
| RedefineEffect of (Microsoft_FStar_Absyn_Syntax.ident * binder Prims.list * term)

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

let is_Mkdecl = (fun _ -> (All.failwith "Not yet implemented:is_Mkdecl"))

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
| Open (_39_157) -> begin
_39_157
end))

let ___KindAbbrev____0 = (fun projectee -> (match (projectee) with
| KindAbbrev (_39_160) -> begin
_39_160
end))

let ___ToplevelLet____0 = (fun projectee -> (match (projectee) with
| ToplevelLet (_39_163) -> begin
_39_163
end))

let ___Main____0 = (fun projectee -> (match (projectee) with
| Main (_39_166) -> begin
_39_166
end))

let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_39_169) -> begin
_39_169
end))

let ___Tycon____0 = (fun projectee -> (match (projectee) with
| Tycon (_39_172) -> begin
_39_172
end))

let ___Val____0 = (fun projectee -> (match (projectee) with
| Val (_39_175) -> begin
_39_175
end))

let ___Exception____0 = (fun projectee -> (match (projectee) with
| Exception (_39_178) -> begin
_39_178
end))

let ___NewEffect____0 = (fun projectee -> (match (projectee) with
| NewEffect (_39_181) -> begin
_39_181
end))

let ___SubEffect____0 = (fun projectee -> (match (projectee) with
| SubEffect (_39_184) -> begin
_39_184
end))

let ___Pragma____0 = (fun projectee -> (match (projectee) with
| Pragma (_39_187) -> begin
_39_187
end))

let ___DefineEffect____0 = (fun projectee -> (match (projectee) with
| DefineEffect (_39_191) -> begin
_39_191
end))

let ___RedefineEffect____0 = (fun projectee -> (match (projectee) with
| RedefineEffect (_39_194) -> begin
_39_194
end))

type modul =
| Module of (Microsoft_FStar_Absyn_Syntax.l__LongIdent * decl Prims.list)
| Interface of (Microsoft_FStar_Absyn_Syntax.l__LongIdent * decl Prims.list * Prims.bool)

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
| Module (_39_197) -> begin
_39_197
end))

let ___Interface____0 = (fun projectee -> (match (projectee) with
| Interface (_39_200) -> begin
_39_200
end))

type file =
modul Prims.list

type inputFragment =
(file, decl Prims.list) Microsoft_FStar_Util.either

let mk_decl = (fun d r -> {d = d; drange = r})

let mk_binder = (fun b r l i -> {b = b; brange = r; blevel = l; aqual = i})

let mk_term = (fun t r l -> {tm = t; range = r; level = l})

let mk_pattern = (fun p r -> {pat = p; prange = r})

let un_curry_abs = (fun ps body -> (match (body.tm) with
| Abs (p', body') -> begin
Abs (((Microsoft_FStar_List.append ps p'), body'))
end
| _39_219 -> begin
Abs ((ps, body))
end))

let mk_function = (fun branches r1 r2 -> (let x = (Microsoft_FStar_Absyn_Util.genident (Some (r1)))
in (let _105_937 = (let _105_936 = (let _105_935 = (let _105_934 = (let _105_933 = (let _105_932 = (let _105_931 = (let _105_930 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in Var (_105_930))
in (mk_term _105_931 r1 Expr))
in (_105_932, branches))
in Match (_105_933))
in (mk_term _105_934 r2 Expr))
in (((mk_pattern (PatVar ((x, false))) r1))::[], _105_935))
in Abs (_105_936))
in (mk_term _105_937 r2 Expr))))

let un_function = (fun p tm -> (match ((p.pat, tm.tm)) with
| (PatVar (_39_227), Abs (pats, body)) -> begin
Some (((mk_pattern (PatApp ((p, pats))) p.prange), body))
end
| _39_235 -> begin
None
end))

let lid_with_range = (fun lid r -> (let _105_946 = (Microsoft_FStar_Absyn_Syntax.path_of_lid lid)
in (Microsoft_FStar_Absyn_Syntax.lid_of_path _105_946 r)))

let to_string_l = (fun sep f l -> (let _105_953 = (Microsoft_FStar_List.map f l)
in (Microsoft_FStar_String.concat sep _105_953)))

let imp_to_string = (fun _39_1 -> (match (_39_1) with
| Hash -> begin
"#"
end
| _39_244 -> begin
""
end))

let rec term_to_string = (fun x -> (match (x.tm) with
| Wild -> begin
"_"
end
| Requires (t, _39_249) -> begin
(let _105_960 = (term_to_string t)
in (Microsoft_FStar_Util.format1 "(requires %s)" _105_960))
end
| Ensures (t, _39_254) -> begin
(let _105_961 = (term_to_string t)
in (Microsoft_FStar_Util.format1 "(ensures %s)" _105_961))
end
| Labeled (t, l, _39_260) -> begin
(let _105_962 = (term_to_string t)
in (Microsoft_FStar_Util.format2 "(labeled %s %s)" l _105_962))
end
| Const (c) -> begin
(Microsoft_FStar_Absyn_Print.const_to_string c)
end
| Op (s, xs) -> begin
(let _105_965 = (let _105_964 = (Microsoft_FStar_List.map (fun x -> (All.pipe_right x term_to_string)) xs)
in (Microsoft_FStar_String.concat ", " _105_964))
in (Microsoft_FStar_Util.format2 "%s(%s)" s _105_965))
end
| Tvar (id) -> begin
id.Microsoft_FStar_Absyn_Syntax.idText
end
| (Var (l)) | (Name (l)) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end
| Construct (l, args) -> begin
(let _105_969 = (Microsoft_FStar_Absyn_Print.sli l)
in (let _105_968 = (to_string_l " " (fun _39_281 -> (match (_39_281) with
| (a, imp) -> begin
(let _105_967 = (term_to_string a)
in (Microsoft_FStar_Util.format2 "%s%s" (imp_to_string imp) _105_967))
end)) args)
in (Microsoft_FStar_Util.format2 "(%s %s)" _105_969 _105_968)))
end
| Abs (pats, t) when (x.level = Expr) -> begin
(let _105_971 = (to_string_l " " pat_to_string pats)
in (let _105_970 = (All.pipe_right t term_to_string)
in (Microsoft_FStar_Util.format2 "(fun %s -> %s)" _105_971 _105_970)))
end
| Abs (pats, t) when (x.level = Type) -> begin
(let _105_973 = (to_string_l " " pat_to_string pats)
in (let _105_972 = (All.pipe_right t term_to_string)
in (Microsoft_FStar_Util.format2 "(fun %s => %s)" _105_973 _105_972)))
end
| App (t1, t2, imp) -> begin
(let _105_975 = (All.pipe_right t1 term_to_string)
in (let _105_974 = (All.pipe_right t2 term_to_string)
in (Microsoft_FStar_Util.format3 "%s %s%s" _105_975 (imp_to_string imp) _105_974)))
end
| Let (false, (pat, tm)::[], body) -> begin
(let _105_978 = (All.pipe_right pat pat_to_string)
in (let _105_977 = (All.pipe_right tm term_to_string)
in (let _105_976 = (All.pipe_right body term_to_string)
in (Microsoft_FStar_Util.format3 "let %s = %s in %s" _105_978 _105_977 _105_976))))
end
| Let (_39_304, lbs, body) -> begin
(let _105_983 = (to_string_l " and " (fun _39_311 -> (match (_39_311) with
| (p, b) -> begin
(let _105_981 = (All.pipe_right p pat_to_string)
in (let _105_980 = (All.pipe_right b term_to_string)
in (Microsoft_FStar_Util.format2 "%s=%s" _105_981 _105_980)))
end)) lbs)
in (let _105_982 = (All.pipe_right body term_to_string)
in (Microsoft_FStar_Util.format2 "let rec %s in %s" _105_983 _105_982)))
end
| Seq (t1, t2) -> begin
(let _105_985 = (All.pipe_right t1 term_to_string)
in (let _105_984 = (All.pipe_right t2 term_to_string)
in (Microsoft_FStar_Util.format2 "%s; %s" _105_985 _105_984)))
end
| If (t1, t2, t3) -> begin
(let _105_988 = (All.pipe_right t1 term_to_string)
in (let _105_987 = (All.pipe_right t2 term_to_string)
in (let _105_986 = (All.pipe_right t3 term_to_string)
in (Microsoft_FStar_Util.format3 "if %s then %s else %s" _105_988 _105_987 _105_986))))
end
| Match (t, branches) -> begin
(let _105_995 = (All.pipe_right t term_to_string)
in (let _105_994 = (to_string_l " | " (fun _39_328 -> (match (_39_328) with
| (p, w, e) -> begin
(let _105_993 = (All.pipe_right p pat_to_string)
in (let _105_992 = (match (w) with
| None -> begin
""
end
| Some (e) -> begin
(let _105_990 = (term_to_string e)
in (Microsoft_FStar_Util.format1 "when %s" _105_990))
end)
in (let _105_991 = (All.pipe_right e term_to_string)
in (Microsoft_FStar_Util.format3 "%s %s -> %s" _105_993 _105_992 _105_991))))
end)) branches)
in (Microsoft_FStar_Util.format2 "match %s with %s" _105_995 _105_994)))
end
| Ascribed (t1, t2) -> begin
(let _105_997 = (All.pipe_right t1 term_to_string)
in (let _105_996 = (All.pipe_right t2 term_to_string)
in (Microsoft_FStar_Util.format2 "(%s : %s)" _105_997 _105_996)))
end
| Record (Some (e), fields) -> begin
(let _105_1002 = (All.pipe_right e term_to_string)
in (let _105_1001 = (to_string_l " " (fun _39_343 -> (match (_39_343) with
| (l, e) -> begin
(let _105_1000 = (Microsoft_FStar_Absyn_Print.sli l)
in (let _105_999 = (All.pipe_right e term_to_string)
in (Microsoft_FStar_Util.format2 "%s=%s" _105_1000 _105_999)))
end)) fields)
in (Microsoft_FStar_Util.format2 "{%s with %s}" _105_1002 _105_1001)))
end
| Record (None, fields) -> begin
(let _105_1006 = (to_string_l " " (fun _39_350 -> (match (_39_350) with
| (l, e) -> begin
(let _105_1005 = (Microsoft_FStar_Absyn_Print.sli l)
in (let _105_1004 = (All.pipe_right e term_to_string)
in (Microsoft_FStar_Util.format2 "%s=%s" _105_1005 _105_1004)))
end)) fields)
in (Microsoft_FStar_Util.format1 "{%s}" _105_1006))
end
| Project (e, l) -> begin
(let _105_1008 = (All.pipe_right e term_to_string)
in (let _105_1007 = (Microsoft_FStar_Absyn_Print.sli l)
in (Microsoft_FStar_Util.format2 "%s.%s" _105_1008 _105_1007)))
end
| Product ([], t) -> begin
(term_to_string t)
end
| Product (b::hd::tl, t) -> begin
(term_to_string (mk_term (Product (((b)::[], (mk_term (Product (((hd)::tl, t))) x.range x.level)))) x.range x.level))
end
| Product (b::[], t) when (x.level = Type) -> begin
(let _105_1010 = (All.pipe_right b binder_to_string)
in (let _105_1009 = (All.pipe_right t term_to_string)
in (Microsoft_FStar_Util.format2 "%s -> %s" _105_1010 _105_1009)))
end
| Product (b::[], t) when (x.level = Kind) -> begin
(let _105_1012 = (All.pipe_right b binder_to_string)
in (let _105_1011 = (All.pipe_right t term_to_string)
in (Microsoft_FStar_Util.format2 "%s => %s" _105_1012 _105_1011)))
end
| Sum (binders, t) -> begin
(let _105_1015 = (let _105_1013 = (All.pipe_right binders (Microsoft_FStar_List.map binder_to_string))
in (All.pipe_right _105_1013 (Microsoft_FStar_String.concat " * ")))
in (let _105_1014 = (All.pipe_right t term_to_string)
in (Microsoft_FStar_Util.format2 "%s * %s" _105_1015 _105_1014)))
end
| QForall (bs, pats, t) -> begin
(let _105_1018 = (to_string_l " " binder_to_string bs)
in (let _105_1017 = (to_string_l "; " term_to_string pats)
in (let _105_1016 = (All.pipe_right t term_to_string)
in (Microsoft_FStar_Util.format3 "forall %s.{:pattern %s} %s" _105_1018 _105_1017 _105_1016))))
end
| QExists (bs, pats, t) -> begin
(let _105_1021 = (to_string_l " " binder_to_string bs)
in (let _105_1020 = (to_string_l "; " term_to_string pats)
in (let _105_1019 = (All.pipe_right t term_to_string)
in (Microsoft_FStar_Util.format3 "exists %s.{:pattern %s} %s" _105_1021 _105_1020 _105_1019))))
end
| Refine (b, t) -> begin
(let _105_1023 = (All.pipe_right b binder_to_string)
in (let _105_1022 = (All.pipe_right t term_to_string)
in (Microsoft_FStar_Util.format2 "%s:{%s}" _105_1023 _105_1022)))
end
| NamedTyp (x, t) -> begin
(let _105_1024 = (All.pipe_right t term_to_string)
in (Microsoft_FStar_Util.format2 "%s:%s" x.Microsoft_FStar_Absyn_Syntax.idText _105_1024))
end
| Paren (t) -> begin
(let _105_1025 = (All.pipe_right t term_to_string)
in (Microsoft_FStar_Util.format1 "(%s)" _105_1025))
end
| Product (bs, t) -> begin
(let _105_1028 = (let _105_1026 = (All.pipe_right bs (Microsoft_FStar_List.map binder_to_string))
in (All.pipe_right _105_1026 (Microsoft_FStar_String.concat ",")))
in (let _105_1027 = (All.pipe_right t term_to_string)
in (Microsoft_FStar_Util.format2 "Unidentified product: [%s] %s" _105_1028 _105_1027)))
end
| t -> begin
(All.failwith "Missing case in term_to_string")
end))
and binder_to_string = (fun x -> (let s = (match (x.b) with
| Variable (i) -> begin
i.Microsoft_FStar_Absyn_Syntax.idText
end
| TVariable (i) -> begin
(Microsoft_FStar_Util.format1 "%s:_" i.Microsoft_FStar_Absyn_Syntax.idText)
end
| (TAnnotated (i, t)) | (Annotated (i, t)) -> begin
(let _105_1030 = (All.pipe_right t term_to_string)
in (Microsoft_FStar_Util.format2 "%s:%s" i.Microsoft_FStar_Absyn_Syntax.idText _105_1030))
end
| NoName (t) -> begin
(All.pipe_right t term_to_string)
end)
in (match (x.aqual) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
(Microsoft_FStar_Util.format1 "#%s" s)
end
| Some (Microsoft_FStar_Absyn_Syntax.Equality) -> begin
(Microsoft_FStar_Util.format1 "=%s" s)
end
| _39_425 -> begin
s
end)))
and pat_to_string = (fun x -> (match (x.pat) with
| PatWild -> begin
"_"
end
| PatConst (c) -> begin
(Microsoft_FStar_Absyn_Print.const_to_string c)
end
| PatApp (p, ps) -> begin
(let _105_1033 = (All.pipe_right p pat_to_string)
in (let _105_1032 = (to_string_l " " pat_to_string ps)
in (Microsoft_FStar_Util.format2 "(%s %s)" _105_1033 _105_1032)))
end
| (PatTvar (i, true)) | (PatVar (i, true)) -> begin
(Microsoft_FStar_Util.format1 "#%s" i.Microsoft_FStar_Absyn_Syntax.idText)
end
| (PatTvar (i, false)) | (PatVar (i, false)) -> begin
i.Microsoft_FStar_Absyn_Syntax.idText
end
| PatName (l) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end
| PatList (l) -> begin
(let _105_1034 = (to_string_l "; " pat_to_string l)
in (Microsoft_FStar_Util.format1 "[%s]" _105_1034))
end
| PatTuple (l, false) -> begin
(let _105_1035 = (to_string_l ", " pat_to_string l)
in (Microsoft_FStar_Util.format1 "(%s)" _105_1035))
end
| PatTuple (l, true) -> begin
(let _105_1036 = (to_string_l ", " pat_to_string l)
in (Microsoft_FStar_Util.format1 "(|%s|)" _105_1036))
end
| PatRecord (l) -> begin
(let _105_1040 = (to_string_l "; " (fun _39_464 -> (match (_39_464) with
| (f, e) -> begin
(let _105_1039 = (Microsoft_FStar_Absyn_Print.sli f)
in (let _105_1038 = (All.pipe_right e pat_to_string)
in (Microsoft_FStar_Util.format2 "%s=%s" _105_1039 _105_1038)))
end)) l)
in (Microsoft_FStar_Util.format1 "{%s}" _105_1040))
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatAscribed (p, t) -> begin
(let _105_1042 = (All.pipe_right p pat_to_string)
in (let _105_1041 = (All.pipe_right t term_to_string)
in (Microsoft_FStar_Util.format2 "(%s:%s)" _105_1042 _105_1041)))
end))

let error = (fun msg tm r -> (let tm = (All.pipe_right tm term_to_string)
in (let tm = (match (((Microsoft_FStar_String.length tm) >= 80)) with
| true -> begin
(let _105_1046 = (Microsoft_FStar_Util.substring tm 0 77)
in (Prims.strcat _105_1046 "..."))
end
| false -> begin
tm
end)
in (Prims.raise (Microsoft_FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat msg "\n") tm), r)))))))

let consPat = (fun r hd tl -> PatApp (((mk_pattern (PatName (Microsoft_FStar_Absyn_Const.cons_lid)) r), (hd)::(tl)::[])))

let consTerm = (fun r hd tl -> (mk_term (Construct ((Microsoft_FStar_Absyn_Const.cons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))

let lexConsTerm = (fun r hd tl -> (mk_term (Construct ((Microsoft_FStar_Absyn_Const.lexcons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))

let mkConsList = (fun r elts -> (let nil = (mk_term (Construct ((Microsoft_FStar_Absyn_Const.nil_lid, []))) r Expr)
in (Microsoft_FStar_List.fold_right (fun e tl -> (consTerm r e tl)) elts nil)))

let mkLexList = (fun r elts -> (let nil = (mk_term (Construct ((Microsoft_FStar_Absyn_Const.lextop_lid, []))) r Expr)
in (Microsoft_FStar_List.fold_right (fun e tl -> (lexConsTerm r e tl)) elts nil)))

let mkApp = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _39_500 -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct ((s, args))) r Un)
end
| _39_504 -> begin
(Microsoft_FStar_List.fold_left (fun t _39_508 -> (match (_39_508) with
| (a, imp) -> begin
(mk_term (App ((t, a, imp))) r Un)
end)) t args)
end)
end))

let mkRefSet = (fun r elts -> (let empty = (let _105_1090 = (let _105_1089 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.set_empty r)
in Var (_105_1089))
in (mk_term _105_1090 r Expr))
in (let ref_constr = (let _105_1092 = (let _105_1091 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.heap_ref r)
in Var (_105_1091))
in (mk_term _105_1092 r Expr))
in (let singleton = (let _105_1094 = (let _105_1093 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.set_singleton r)
in Var (_105_1093))
in (mk_term _105_1094 r Expr))
in (let union = (let _105_1096 = (let _105_1095 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.set_union r)
in Var (_105_1095))
in (mk_term _105_1096 r Expr))
in (Microsoft_FStar_List.fold_right (fun e tl -> (let e = (mkApp ref_constr (((e, Nothing))::[]) r)
in (let single_e = (mkApp singleton (((e, Nothing))::[]) r)
in (mkApp union (((single_e, Nothing))::((tl, Nothing))::[]) r)))) elts empty))))))

let mkExplicitApp = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _39_524 -> begin
(match (t.tm) with
| Name (s) -> begin
(let _105_1108 = (let _105_1107 = (let _105_1106 = (Microsoft_FStar_List.map (fun a -> (a, Nothing)) args)
in (s, _105_1106))
in Construct (_105_1107))
in (mk_term _105_1108 r Un))
end
| _39_529 -> begin
(Microsoft_FStar_List.fold_left (fun t a -> (mk_term (App ((t, a, Nothing))) r Un)) t args)
end)
end))

let mkAdmitMagic = (fun r -> (let unit_const = (mk_term (Const (Microsoft_FStar_Absyn_Syntax.Const_unit)) r Expr)
in (let admit = (let admit_name = (let _105_1114 = (let _105_1113 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.admit_lid r)
in Var (_105_1113))
in (mk_term _105_1114 r Expr))
in (mkExplicitApp admit_name ((unit_const)::[]) r))
in (let magic = (let magic_name = (let _105_1116 = (let _105_1115 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.magic_lid r)
in Var (_105_1115))
in (mk_term _105_1116 r Expr))
in (mkExplicitApp magic_name ((unit_const)::[]) r))
in (let admit_magic = (mk_term (Seq ((admit, magic))) r Expr)
in admit_magic)))))

let mkWildAdmitMagic = (fun r -> (let _105_1118 = (mkAdmitMagic r)
in ((mk_pattern PatWild r), None, _105_1118)))

let focusBranches = (fun branches r -> (let should_filter = (Microsoft_FStar_Util.for_some Prims.fst branches)
in (match (should_filter) with
| true -> begin
(let _39_543 = (Microsoft_FStar_Tc_Errors.warn r "Focusing on only some cases")
in (let focussed = (let _105_1121 = (Microsoft_FStar_List.filter Prims.fst branches)
in (All.pipe_right _105_1121 (Microsoft_FStar_List.map Prims.snd)))
in (let _105_1123 = (let _105_1122 = (mkWildAdmitMagic r)
in (_105_1122)::[])
in (Microsoft_FStar_List.append focussed _105_1123))))
end
| false -> begin
(All.pipe_right branches (Microsoft_FStar_List.map Prims.snd))
end)))

let focusLetBindings = (fun lbs r -> (let should_filter = (Microsoft_FStar_Util.for_some Prims.fst lbs)
in (match (should_filter) with
| true -> begin
(let _39_549 = (Microsoft_FStar_Tc_Errors.warn r "Focusing on only some cases in this (mutually) recursive definition")
in (Microsoft_FStar_List.map (fun _39_553 -> (match (_39_553) with
| (f, lb) -> begin
(match (f) with
| true -> begin
lb
end
| false -> begin
(let _105_1127 = (mkAdmitMagic r)
in ((Prims.fst lb), _105_1127))
end)
end)) lbs))
end
| false -> begin
(All.pipe_right lbs (Microsoft_FStar_List.map Prims.snd))
end)))

let mkFsTypApp = (fun t args r -> (let _105_1135 = (Microsoft_FStar_List.map (fun a -> (a, FsTypApp)) args)
in (mkApp t _105_1135 r)))

let mkTuple = (fun args r -> (let cons = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid (Microsoft_FStar_List.length args) r)
in (let _105_1141 = (Microsoft_FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _105_1141 r))))

let mkDTuple = (fun args r -> (let cons = (Microsoft_FStar_Absyn_Util.mk_dtuple_data_lid (Microsoft_FStar_List.length args) r)
in (let _105_1147 = (Microsoft_FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _105_1147 r))))

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
| Refine ({b = Annotated (x, t); brange = _39_585; blevel = _39_583; aqual = _39_581}, t') -> begin
Some ((x, t, Some (t')))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| _39_597 -> begin
None
end))




