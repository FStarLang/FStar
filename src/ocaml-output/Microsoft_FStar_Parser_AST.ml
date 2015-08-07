
type level =
| Un
| Expr
| Type
| Kind
| Formula

let is_Un = (fun ( _discr_ ) -> (match (_discr_) with
| Un -> begin
true
end
| _ -> begin
false
end))

let is_Expr = (fun ( _discr_ ) -> (match (_discr_) with
| Expr -> begin
true
end
| _ -> begin
false
end))

let is_Type = (fun ( _discr_ ) -> (match (_discr_) with
| Type -> begin
true
end
| _ -> begin
false
end))

let is_Kind = (fun ( _discr_ ) -> (match (_discr_) with
| Kind -> begin
true
end
| _ -> begin
false
end))

let is_Formula = (fun ( _discr_ ) -> (match (_discr_) with
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

let is_FsTypApp = (fun ( _discr_ ) -> (match (_discr_) with
| FsTypApp -> begin
true
end
| _ -> begin
false
end))

let is_Hash = (fun ( _discr_ ) -> (match (_discr_) with
| Hash -> begin
true
end
| _ -> begin
false
end))

let is_Nothing = (fun ( _discr_ ) -> (match (_discr_) with
| Nothing -> begin
true
end
| _ -> begin
false
end))

type term' =
| Wild
| Const of Microsoft_FStar_Absyn_Syntax.sconst
| Op of (string * term list)
| Tvar of Microsoft_FStar_Absyn_Syntax.ident
| Var of lid
| Name of lid
| Construct of (lid * (term * imp) list)
| Abs of (pattern list * term)
| App of (term * term * imp)
| Let of (bool * (pattern * term) list * term)
| Seq of (term * term)
| If of (term * term * term)
| Match of (term * branch list)
| TryWith of (term * branch list)
| Ascribed of (term * term)
| Record of (term option * (lid * term) list)
| Project of (term * lid)
| Product of (binder list * term)
| Sum of (binder list * term)
| QForall of (binder list * term list * term)
| QExists of (binder list * term list * term)
| Refine of (binder * term)
| NamedTyp of (Microsoft_FStar_Absyn_Syntax.ident * term)
| Paren of term
| Requires of (term * string option)
| Ensures of (term * string option)
| Labeled of (term * string * bool) 
 and term =
{tm : term'; range : Support.Microsoft.FStar.Range.range; level : level} 
 and binder' =
| Variable of Microsoft_FStar_Absyn_Syntax.ident
| TVariable of Microsoft_FStar_Absyn_Syntax.ident
| Annotated of (Microsoft_FStar_Absyn_Syntax.ident * term)
| TAnnotated of (Microsoft_FStar_Absyn_Syntax.ident * term)
| NoName of term 
 and binder =
{b : binder'; brange : Support.Microsoft.FStar.Range.range; blevel : level; aqual : Microsoft_FStar_Absyn_Syntax.aqual} 
 and pattern' =
| PatWild
| PatConst of Microsoft_FStar_Absyn_Syntax.sconst
| PatApp of (pattern * pattern list)
| PatVar of (Microsoft_FStar_Absyn_Syntax.ident * bool)
| PatName of lid
| PatTvar of (Microsoft_FStar_Absyn_Syntax.ident * bool)
| PatList of pattern list
| PatTuple of (pattern list * bool)
| PatRecord of (lid * pattern) list
| PatAscribed of (pattern * term)
| PatOr of pattern list 
 and pattern =
{pat : pattern'; prange : Support.Microsoft.FStar.Range.range} 
 and branch =
(pattern * term option * term)

let is_Wild = (fun ( _discr_ ) -> (match (_discr_) with
| Wild -> begin
true
end
| _ -> begin
false
end))

let is_Const = (fun ( _discr_ ) -> (match (_discr_) with
| Const (_) -> begin
true
end
| _ -> begin
false
end))

let is_Op = (fun ( _discr_ ) -> (match (_discr_) with
| Op (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tvar = (fun ( _discr_ ) -> (match (_discr_) with
| Tvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Var = (fun ( _discr_ ) -> (match (_discr_) with
| Var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Name = (fun ( _discr_ ) -> (match (_discr_) with
| Name (_) -> begin
true
end
| _ -> begin
false
end))

let is_Construct = (fun ( _discr_ ) -> (match (_discr_) with
| Construct (_) -> begin
true
end
| _ -> begin
false
end))

let is_Abs = (fun ( _discr_ ) -> (match (_discr_) with
| Abs (_) -> begin
true
end
| _ -> begin
false
end))

let is_App = (fun ( _discr_ ) -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))

let is_Let = (fun ( _discr_ ) -> (match (_discr_) with
| Let (_) -> begin
true
end
| _ -> begin
false
end))

let is_Seq = (fun ( _discr_ ) -> (match (_discr_) with
| Seq (_) -> begin
true
end
| _ -> begin
false
end))

let is_If = (fun ( _discr_ ) -> (match (_discr_) with
| If (_) -> begin
true
end
| _ -> begin
false
end))

let is_Match = (fun ( _discr_ ) -> (match (_discr_) with
| Match (_) -> begin
true
end
| _ -> begin
false
end))

let is_TryWith = (fun ( _discr_ ) -> (match (_discr_) with
| TryWith (_) -> begin
true
end
| _ -> begin
false
end))

let is_Ascribed = (fun ( _discr_ ) -> (match (_discr_) with
| Ascribed (_) -> begin
true
end
| _ -> begin
false
end))

let is_Record = (fun ( _discr_ ) -> (match (_discr_) with
| Record (_) -> begin
true
end
| _ -> begin
false
end))

let is_Project = (fun ( _discr_ ) -> (match (_discr_) with
| Project (_) -> begin
true
end
| _ -> begin
false
end))

let is_Product = (fun ( _discr_ ) -> (match (_discr_) with
| Product (_) -> begin
true
end
| _ -> begin
false
end))

let is_Sum = (fun ( _discr_ ) -> (match (_discr_) with
| Sum (_) -> begin
true
end
| _ -> begin
false
end))

let is_QForall = (fun ( _discr_ ) -> (match (_discr_) with
| QForall (_) -> begin
true
end
| _ -> begin
false
end))

let is_QExists = (fun ( _discr_ ) -> (match (_discr_) with
| QExists (_) -> begin
true
end
| _ -> begin
false
end))

let is_Refine = (fun ( _discr_ ) -> (match (_discr_) with
| Refine (_) -> begin
true
end
| _ -> begin
false
end))

let is_NamedTyp = (fun ( _discr_ ) -> (match (_discr_) with
| NamedTyp (_) -> begin
true
end
| _ -> begin
false
end))

let is_Paren = (fun ( _discr_ ) -> (match (_discr_) with
| Paren (_) -> begin
true
end
| _ -> begin
false
end))

let is_Requires = (fun ( _discr_ ) -> (match (_discr_) with
| Requires (_) -> begin
true
end
| _ -> begin
false
end))

let is_Ensures = (fun ( _discr_ ) -> (match (_discr_) with
| Ensures (_) -> begin
true
end
| _ -> begin
false
end))

let is_Labeled = (fun ( _discr_ ) -> (match (_discr_) with
| Labeled (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkterm = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkterm"))

let is_Variable = (fun ( _discr_ ) -> (match (_discr_) with
| Variable (_) -> begin
true
end
| _ -> begin
false
end))

let is_TVariable = (fun ( _discr_ ) -> (match (_discr_) with
| TVariable (_) -> begin
true
end
| _ -> begin
false
end))

let is_Annotated = (fun ( _discr_ ) -> (match (_discr_) with
| Annotated (_) -> begin
true
end
| _ -> begin
false
end))

let is_TAnnotated = (fun ( _discr_ ) -> (match (_discr_) with
| TAnnotated (_) -> begin
true
end
| _ -> begin
false
end))

let is_NoName = (fun ( _discr_ ) -> (match (_discr_) with
| NoName (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkbinder = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkbinder"))

let is_PatWild = (fun ( _discr_ ) -> (match (_discr_) with
| PatWild -> begin
true
end
| _ -> begin
false
end))

let is_PatConst = (fun ( _discr_ ) -> (match (_discr_) with
| PatConst (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatApp = (fun ( _discr_ ) -> (match (_discr_) with
| PatApp (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatVar = (fun ( _discr_ ) -> (match (_discr_) with
| PatVar (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatName = (fun ( _discr_ ) -> (match (_discr_) with
| PatName (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatTvar = (fun ( _discr_ ) -> (match (_discr_) with
| PatTvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatList = (fun ( _discr_ ) -> (match (_discr_) with
| PatList (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatTuple = (fun ( _discr_ ) -> (match (_discr_) with
| PatTuple (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatRecord = (fun ( _discr_ ) -> (match (_discr_) with
| PatRecord (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatAscribed = (fun ( _discr_ ) -> (match (_discr_) with
| PatAscribed (_) -> begin
true
end
| _ -> begin
false
end))

let is_PatOr = (fun ( _discr_ ) -> (match (_discr_) with
| PatOr (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkpattern = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkpattern"))

let ___Const____0 = (fun ( projectee ) -> (match (projectee) with
| Const (_39_13) -> begin
_39_13
end))

let ___Op____0 = (fun ( projectee ) -> (match (projectee) with
| Op (_39_16) -> begin
_39_16
end))

let ___Tvar____0 = (fun ( projectee ) -> (match (projectee) with
| Tvar (_39_19) -> begin
_39_19
end))

let ___Var____0 = (fun ( projectee ) -> (match (projectee) with
| Var (_39_22) -> begin
_39_22
end))

let ___Name____0 = (fun ( projectee ) -> (match (projectee) with
| Name (_39_25) -> begin
_39_25
end))

let ___Construct____0 = (fun ( projectee ) -> (match (projectee) with
| Construct (_39_28) -> begin
_39_28
end))

let ___Abs____0 = (fun ( projectee ) -> (match (projectee) with
| Abs (_39_31) -> begin
_39_31
end))

let ___App____0 = (fun ( projectee ) -> (match (projectee) with
| App (_39_34) -> begin
_39_34
end))

let ___Let____0 = (fun ( projectee ) -> (match (projectee) with
| Let (_39_37) -> begin
_39_37
end))

let ___Seq____0 = (fun ( projectee ) -> (match (projectee) with
| Seq (_39_40) -> begin
_39_40
end))

let ___If____0 = (fun ( projectee ) -> (match (projectee) with
| If (_39_43) -> begin
_39_43
end))

let ___Match____0 = (fun ( projectee ) -> (match (projectee) with
| Match (_39_46) -> begin
_39_46
end))

let ___TryWith____0 = (fun ( projectee ) -> (match (projectee) with
| TryWith (_39_49) -> begin
_39_49
end))

let ___Ascribed____0 = (fun ( projectee ) -> (match (projectee) with
| Ascribed (_39_52) -> begin
_39_52
end))

let ___Record____0 = (fun ( projectee ) -> (match (projectee) with
| Record (_39_55) -> begin
_39_55
end))

let ___Project____0 = (fun ( projectee ) -> (match (projectee) with
| Project (_39_58) -> begin
_39_58
end))

let ___Product____0 = (fun ( projectee ) -> (match (projectee) with
| Product (_39_61) -> begin
_39_61
end))

let ___Sum____0 = (fun ( projectee ) -> (match (projectee) with
| Sum (_39_64) -> begin
_39_64
end))

let ___QForall____0 = (fun ( projectee ) -> (match (projectee) with
| QForall (_39_67) -> begin
_39_67
end))

let ___QExists____0 = (fun ( projectee ) -> (match (projectee) with
| QExists (_39_70) -> begin
_39_70
end))

let ___Refine____0 = (fun ( projectee ) -> (match (projectee) with
| Refine (_39_73) -> begin
_39_73
end))

let ___NamedTyp____0 = (fun ( projectee ) -> (match (projectee) with
| NamedTyp (_39_76) -> begin
_39_76
end))

let ___Paren____0 = (fun ( projectee ) -> (match (projectee) with
| Paren (_39_79) -> begin
_39_79
end))

let ___Requires____0 = (fun ( projectee ) -> (match (projectee) with
| Requires (_39_82) -> begin
_39_82
end))

let ___Ensures____0 = (fun ( projectee ) -> (match (projectee) with
| Ensures (_39_85) -> begin
_39_85
end))

let ___Labeled____0 = (fun ( projectee ) -> (match (projectee) with
| Labeled (_39_88) -> begin
_39_88
end))

let ___Variable____0 = (fun ( projectee ) -> (match (projectee) with
| Variable (_39_92) -> begin
_39_92
end))

let ___TVariable____0 = (fun ( projectee ) -> (match (projectee) with
| TVariable (_39_95) -> begin
_39_95
end))

let ___Annotated____0 = (fun ( projectee ) -> (match (projectee) with
| Annotated (_39_98) -> begin
_39_98
end))

let ___TAnnotated____0 = (fun ( projectee ) -> (match (projectee) with
| TAnnotated (_39_101) -> begin
_39_101
end))

let ___NoName____0 = (fun ( projectee ) -> (match (projectee) with
| NoName (_39_104) -> begin
_39_104
end))

let ___PatConst____0 = (fun ( projectee ) -> (match (projectee) with
| PatConst (_39_108) -> begin
_39_108
end))

let ___PatApp____0 = (fun ( projectee ) -> (match (projectee) with
| PatApp (_39_111) -> begin
_39_111
end))

let ___PatVar____0 = (fun ( projectee ) -> (match (projectee) with
| PatVar (_39_114) -> begin
_39_114
end))

let ___PatName____0 = (fun ( projectee ) -> (match (projectee) with
| PatName (_39_117) -> begin
_39_117
end))

let ___PatTvar____0 = (fun ( projectee ) -> (match (projectee) with
| PatTvar (_39_120) -> begin
_39_120
end))

let ___PatList____0 = (fun ( projectee ) -> (match (projectee) with
| PatList (_39_123) -> begin
_39_123
end))

let ___PatTuple____0 = (fun ( projectee ) -> (match (projectee) with
| PatTuple (_39_126) -> begin
_39_126
end))

let ___PatRecord____0 = (fun ( projectee ) -> (match (projectee) with
| PatRecord (_39_129) -> begin
_39_129
end))

let ___PatAscribed____0 = (fun ( projectee ) -> (match (projectee) with
| PatAscribed (_39_132) -> begin
_39_132
end))

let ___PatOr____0 = (fun ( projectee ) -> (match (projectee) with
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
| TyconAbstract of (Microsoft_FStar_Absyn_Syntax.ident * binder list * knd option)
| TyconAbbrev of (Microsoft_FStar_Absyn_Syntax.ident * binder list * knd option * term)
| TyconRecord of (Microsoft_FStar_Absyn_Syntax.ident * binder list * knd option * (Microsoft_FStar_Absyn_Syntax.ident * term) list)
| TyconVariant of (Microsoft_FStar_Absyn_Syntax.ident * binder list * knd option * (Microsoft_FStar_Absyn_Syntax.ident * term option * bool) list)

let is_TyconAbstract = (fun ( _discr_ ) -> (match (_discr_) with
| TyconAbstract (_) -> begin
true
end
| _ -> begin
false
end))

let is_TyconAbbrev = (fun ( _discr_ ) -> (match (_discr_) with
| TyconAbbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_TyconRecord = (fun ( _discr_ ) -> (match (_discr_) with
| TyconRecord (_) -> begin
true
end
| _ -> begin
false
end))

let is_TyconVariant = (fun ( _discr_ ) -> (match (_discr_) with
| TyconVariant (_) -> begin
true
end
| _ -> begin
false
end))

let ___TyconAbstract____0 = (fun ( projectee ) -> (match (projectee) with
| TyconAbstract (_39_139) -> begin
_39_139
end))

let ___TyconAbbrev____0 = (fun ( projectee ) -> (match (projectee) with
| TyconAbbrev (_39_142) -> begin
_39_142
end))

let ___TyconRecord____0 = (fun ( projectee ) -> (match (projectee) with
| TyconRecord (_39_145) -> begin
_39_145
end))

let ___TyconVariant____0 = (fun ( projectee ) -> (match (projectee) with
| TyconVariant (_39_148) -> begin
_39_148
end))

type qualifiers =
Microsoft_FStar_Absyn_Syntax.qualifier list

type lift =
{msource : lid; mdest : lid; lift_op : term}

let is_Mklift = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mklift"))

type decl' =
| Open of lid
| KindAbbrev of (Microsoft_FStar_Absyn_Syntax.ident * binder list * knd)
| ToplevelLet of (bool * (pattern * term) list)
| Main of term
| Assume of (qualifiers * Microsoft_FStar_Absyn_Syntax.ident * term)
| Tycon of (qualifiers * tycon list)
| Val of (qualifiers * Microsoft_FStar_Absyn_Syntax.ident * term)
| Exception of (Microsoft_FStar_Absyn_Syntax.ident * term option)
| NewEffect of (qualifiers * effect_decl)
| SubEffect of lift
| Pragma of Microsoft_FStar_Absyn_Syntax.pragma 
 and decl =
{d : decl'; drange : Support.Microsoft.FStar.Range.range} 
 and effect_decl =
| DefineEffect of (Microsoft_FStar_Absyn_Syntax.ident * binder list * term * decl list)
| RedefineEffect of (Microsoft_FStar_Absyn_Syntax.ident * binder list * term)

let is_Open = (fun ( _discr_ ) -> (match (_discr_) with
| Open (_) -> begin
true
end
| _ -> begin
false
end))

let is_KindAbbrev = (fun ( _discr_ ) -> (match (_discr_) with
| KindAbbrev (_) -> begin
true
end
| _ -> begin
false
end))

let is_ToplevelLet = (fun ( _discr_ ) -> (match (_discr_) with
| ToplevelLet (_) -> begin
true
end
| _ -> begin
false
end))

let is_Main = (fun ( _discr_ ) -> (match (_discr_) with
| Main (_) -> begin
true
end
| _ -> begin
false
end))

let is_Assume = (fun ( _discr_ ) -> (match (_discr_) with
| Assume (_) -> begin
true
end
| _ -> begin
false
end))

let is_Tycon = (fun ( _discr_ ) -> (match (_discr_) with
| Tycon (_) -> begin
true
end
| _ -> begin
false
end))

let is_Val = (fun ( _discr_ ) -> (match (_discr_) with
| Val (_) -> begin
true
end
| _ -> begin
false
end))

let is_Exception = (fun ( _discr_ ) -> (match (_discr_) with
| Exception (_) -> begin
true
end
| _ -> begin
false
end))

let is_NewEffect = (fun ( _discr_ ) -> (match (_discr_) with
| NewEffect (_) -> begin
true
end
| _ -> begin
false
end))

let is_SubEffect = (fun ( _discr_ ) -> (match (_discr_) with
| SubEffect (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pragma = (fun ( _discr_ ) -> (match (_discr_) with
| Pragma (_) -> begin
true
end
| _ -> begin
false
end))

let is_Mkdecl = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkdecl"))

let is_DefineEffect = (fun ( _discr_ ) -> (match (_discr_) with
| DefineEffect (_) -> begin
true
end
| _ -> begin
false
end))

let is_RedefineEffect = (fun ( _discr_ ) -> (match (_discr_) with
| RedefineEffect (_) -> begin
true
end
| _ -> begin
false
end))

let ___Open____0 = (fun ( projectee ) -> (match (projectee) with
| Open (_39_157) -> begin
_39_157
end))

let ___KindAbbrev____0 = (fun ( projectee ) -> (match (projectee) with
| KindAbbrev (_39_160) -> begin
_39_160
end))

let ___ToplevelLet____0 = (fun ( projectee ) -> (match (projectee) with
| ToplevelLet (_39_163) -> begin
_39_163
end))

let ___Main____0 = (fun ( projectee ) -> (match (projectee) with
| Main (_39_166) -> begin
_39_166
end))

let ___Assume____0 = (fun ( projectee ) -> (match (projectee) with
| Assume (_39_169) -> begin
_39_169
end))

let ___Tycon____0 = (fun ( projectee ) -> (match (projectee) with
| Tycon (_39_172) -> begin
_39_172
end))

let ___Val____0 = (fun ( projectee ) -> (match (projectee) with
| Val (_39_175) -> begin
_39_175
end))

let ___Exception____0 = (fun ( projectee ) -> (match (projectee) with
| Exception (_39_178) -> begin
_39_178
end))

let ___NewEffect____0 = (fun ( projectee ) -> (match (projectee) with
| NewEffect (_39_181) -> begin
_39_181
end))

let ___SubEffect____0 = (fun ( projectee ) -> (match (projectee) with
| SubEffect (_39_184) -> begin
_39_184
end))

let ___Pragma____0 = (fun ( projectee ) -> (match (projectee) with
| Pragma (_39_187) -> begin
_39_187
end))

let ___DefineEffect____0 = (fun ( projectee ) -> (match (projectee) with
| DefineEffect (_39_191) -> begin
_39_191
end))

let ___RedefineEffect____0 = (fun ( projectee ) -> (match (projectee) with
| RedefineEffect (_39_194) -> begin
_39_194
end))

type modul =
| Module of (Microsoft_FStar_Absyn_Syntax.l__LongIdent * decl list)
| Interface of (Microsoft_FStar_Absyn_Syntax.l__LongIdent * decl list * bool)

let is_Module = (fun ( _discr_ ) -> (match (_discr_) with
| Module (_) -> begin
true
end
| _ -> begin
false
end))

let is_Interface = (fun ( _discr_ ) -> (match (_discr_) with
| Interface (_) -> begin
true
end
| _ -> begin
false
end))

let ___Module____0 = (fun ( projectee ) -> (match (projectee) with
| Module (_39_197) -> begin
_39_197
end))

let ___Interface____0 = (fun ( projectee ) -> (match (projectee) with
| Interface (_39_200) -> begin
_39_200
end))

type file =
modul list

type inputFragment =
(file, decl list) Support.Microsoft.FStar.Util.either

let mk_decl = (fun ( d ) ( r ) -> {d = d; drange = r})

let mk_binder = (fun ( b ) ( r ) ( l ) ( i ) -> {b = b; brange = r; blevel = l; aqual = i})

let mk_term = (fun ( t ) ( r ) ( l ) -> {tm = t; range = r; level = l})

let mk_pattern = (fun ( p ) ( r ) -> {pat = p; prange = r})

let un_curry_abs = (fun ( ps ) ( body ) -> (match (body.tm) with
| Abs ((p', body')) -> begin
Abs (((Support.List.append ps p'), body'))
end
| _39_219 -> begin
Abs ((ps, body))
end))

let mk_function = (fun ( branches ) ( r1 ) ( r2 ) -> (let x = (Microsoft_FStar_Absyn_Util.genident (Some (r1)))
in (let _70_19898 = (let _70_19897 = (let _70_19896 = (let _70_19895 = (let _70_19894 = (let _70_19893 = (let _70_19892 = (let _70_19891 = (Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[]))
in Var (_70_19891))
in (mk_term _70_19892 r1 Expr))
in (_70_19893, branches))
in Match (_70_19894))
in (mk_term _70_19895 r2 Expr))
in (((mk_pattern (PatVar ((x, false))) r1))::[], _70_19896))
in Abs (_70_19897))
in (mk_term _70_19898 r2 Expr))))

let un_function = (fun ( p ) ( tm ) -> (match ((p.pat, tm.tm)) with
| (PatVar (_39_227), Abs ((pats, body))) -> begin
Some (((mk_pattern (PatApp ((p, pats))) p.prange), body))
end
| _39_235 -> begin
None
end))

let lid_with_range = (fun ( lid ) ( r ) -> (let _70_19907 = (Microsoft_FStar_Absyn_Syntax.path_of_lid lid)
in (Microsoft_FStar_Absyn_Syntax.lid_of_path _70_19907 r)))

let to_string_l = (fun ( sep ) ( f ) ( l ) -> (let _70_19914 = (Support.List.map f l)
in (Support.String.concat sep _70_19914)))

let imp_to_string = (fun ( _39_1 ) -> (match (_39_1) with
| Hash -> begin
"#"
end
| _39_244 -> begin
""
end))

let rec term_to_string = (fun ( x ) -> (match (x.tm) with
| Wild -> begin
"_"
end
| Requires ((t, _39_249)) -> begin
(let _70_19921 = (term_to_string t)
in (Support.Microsoft.FStar.Util.format1 "(requires %s)" _70_19921))
end
| Ensures ((t, _39_254)) -> begin
(let _70_19922 = (term_to_string t)
in (Support.Microsoft.FStar.Util.format1 "(ensures %s)" _70_19922))
end
| Labeled ((t, l, _39_260)) -> begin
(let _70_19923 = (term_to_string t)
in (Support.Microsoft.FStar.Util.format2 "(labeled %s %s)" l _70_19923))
end
| Const (c) -> begin
(Microsoft_FStar_Absyn_Print.const_to_string c)
end
| Op ((s, xs)) -> begin
(let _70_19926 = (let _70_19925 = (Support.List.map (fun ( x ) -> (Support.All.pipe_right x term_to_string)) xs)
in (Support.String.concat ", " _70_19925))
in (Support.Microsoft.FStar.Util.format2 "%s(%s)" s _70_19926))
end
| Tvar (id) -> begin
id.Microsoft_FStar_Absyn_Syntax.idText
end
| (Var (l)) | (Name (l)) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end
| Construct ((l, args)) -> begin
(let _70_19930 = (Microsoft_FStar_Absyn_Print.sli l)
in (let _70_19929 = (to_string_l " " (fun ( _39_281 ) -> (match (_39_281) with
| (a, imp) -> begin
(let _70_19928 = (term_to_string a)
in (Support.Microsoft.FStar.Util.format2 "%s%s" (imp_to_string imp) _70_19928))
end)) args)
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _70_19930 _70_19929)))
end
| Abs ((pats, t)) when (x.level = Expr) -> begin
(let _70_19932 = (to_string_l " " pat_to_string pats)
in (let _70_19931 = (Support.All.pipe_right t term_to_string)
in (Support.Microsoft.FStar.Util.format2 "(fun %s -> %s)" _70_19932 _70_19931)))
end
| Abs ((pats, t)) when (x.level = Type) -> begin
(let _70_19934 = (to_string_l " " pat_to_string pats)
in (let _70_19933 = (Support.All.pipe_right t term_to_string)
in (Support.Microsoft.FStar.Util.format2 "(fun %s => %s)" _70_19934 _70_19933)))
end
| App ((t1, t2, imp)) -> begin
(let _70_19936 = (Support.All.pipe_right t1 term_to_string)
in (let _70_19935 = (Support.All.pipe_right t2 term_to_string)
in (Support.Microsoft.FStar.Util.format3 "%s %s%s" _70_19936 (imp_to_string imp) _70_19935)))
end
| Let ((false, (pat, tm)::[], body)) -> begin
(let _70_19939 = (Support.All.pipe_right pat pat_to_string)
in (let _70_19938 = (Support.All.pipe_right tm term_to_string)
in (let _70_19937 = (Support.All.pipe_right body term_to_string)
in (Support.Microsoft.FStar.Util.format3 "let %s = %s in %s" _70_19939 _70_19938 _70_19937))))
end
| Let ((_39_304, lbs, body)) -> begin
(let _70_19944 = (to_string_l " and " (fun ( _39_311 ) -> (match (_39_311) with
| (p, b) -> begin
(let _70_19942 = (Support.All.pipe_right p pat_to_string)
in (let _70_19941 = (Support.All.pipe_right b term_to_string)
in (Support.Microsoft.FStar.Util.format2 "%s=%s" _70_19942 _70_19941)))
end)) lbs)
in (let _70_19943 = (Support.All.pipe_right body term_to_string)
in (Support.Microsoft.FStar.Util.format2 "let rec %s in %s" _70_19944 _70_19943)))
end
| Seq ((t1, t2)) -> begin
(let _70_19946 = (Support.All.pipe_right t1 term_to_string)
in (let _70_19945 = (Support.All.pipe_right t2 term_to_string)
in (Support.Microsoft.FStar.Util.format2 "%s; %s" _70_19946 _70_19945)))
end
| If ((t1, t2, t3)) -> begin
(let _70_19949 = (Support.All.pipe_right t1 term_to_string)
in (let _70_19948 = (Support.All.pipe_right t2 term_to_string)
in (let _70_19947 = (Support.All.pipe_right t3 term_to_string)
in (Support.Microsoft.FStar.Util.format3 "if %s then %s else %s" _70_19949 _70_19948 _70_19947))))
end
| Match ((t, branches)) -> begin
(let _70_19956 = (Support.All.pipe_right t term_to_string)
in (let _70_19955 = (to_string_l " | " (fun ( _39_328 ) -> (match (_39_328) with
| (p, w, e) -> begin
(let _70_19954 = (Support.All.pipe_right p pat_to_string)
in (let _70_19953 = (match (w) with
| None -> begin
""
end
| Some (e) -> begin
(let _70_19951 = (term_to_string e)
in (Support.Microsoft.FStar.Util.format1 "when %s" _70_19951))
end)
in (let _70_19952 = (Support.All.pipe_right e term_to_string)
in (Support.Microsoft.FStar.Util.format3 "%s %s -> %s" _70_19954 _70_19953 _70_19952))))
end)) branches)
in (Support.Microsoft.FStar.Util.format2 "match %s with %s" _70_19956 _70_19955)))
end
| Ascribed ((t1, t2)) -> begin
(let _70_19958 = (Support.All.pipe_right t1 term_to_string)
in (let _70_19957 = (Support.All.pipe_right t2 term_to_string)
in (Support.Microsoft.FStar.Util.format2 "(%s : %s)" _70_19958 _70_19957)))
end
| Record ((Some (e), fields)) -> begin
(let _70_19963 = (Support.All.pipe_right e term_to_string)
in (let _70_19962 = (to_string_l " " (fun ( _39_343 ) -> (match (_39_343) with
| (l, e) -> begin
(let _70_19961 = (Microsoft_FStar_Absyn_Print.sli l)
in (let _70_19960 = (Support.All.pipe_right e term_to_string)
in (Support.Microsoft.FStar.Util.format2 "%s=%s" _70_19961 _70_19960)))
end)) fields)
in (Support.Microsoft.FStar.Util.format2 "{%s with %s}" _70_19963 _70_19962)))
end
| Record ((None, fields)) -> begin
(let _70_19967 = (to_string_l " " (fun ( _39_350 ) -> (match (_39_350) with
| (l, e) -> begin
(let _70_19966 = (Microsoft_FStar_Absyn_Print.sli l)
in (let _70_19965 = (Support.All.pipe_right e term_to_string)
in (Support.Microsoft.FStar.Util.format2 "%s=%s" _70_19966 _70_19965)))
end)) fields)
in (Support.Microsoft.FStar.Util.format1 "{%s}" _70_19967))
end
| Project ((e, l)) -> begin
(let _70_19969 = (Support.All.pipe_right e term_to_string)
in (let _70_19968 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format2 "%s.%s" _70_19969 _70_19968)))
end
| Product (([], t)) -> begin
(term_to_string t)
end
| Product ((b::hd::tl, t)) -> begin
(term_to_string (mk_term (Product (((b)::[], (mk_term (Product (((hd)::tl, t))) x.range x.level)))) x.range x.level))
end
| Product ((b::[], t)) when (x.level = Type) -> begin
(let _70_19971 = (Support.All.pipe_right b binder_to_string)
in (let _70_19970 = (Support.All.pipe_right t term_to_string)
in (Support.Microsoft.FStar.Util.format2 "%s -> %s" _70_19971 _70_19970)))
end
| Product ((b::[], t)) when (x.level = Kind) -> begin
(let _70_19973 = (Support.All.pipe_right b binder_to_string)
in (let _70_19972 = (Support.All.pipe_right t term_to_string)
in (Support.Microsoft.FStar.Util.format2 "%s => %s" _70_19973 _70_19972)))
end
| Sum ((binders, t)) -> begin
(let _70_19976 = (let _70_19974 = (Support.All.pipe_right binders (Support.List.map binder_to_string))
in (Support.All.pipe_right _70_19974 (Support.String.concat " * ")))
in (let _70_19975 = (Support.All.pipe_right t term_to_string)
in (Support.Microsoft.FStar.Util.format2 "%s * %s" _70_19976 _70_19975)))
end
| QForall ((bs, pats, t)) -> begin
(let _70_19979 = (to_string_l " " binder_to_string bs)
in (let _70_19978 = (to_string_l "; " term_to_string pats)
in (let _70_19977 = (Support.All.pipe_right t term_to_string)
in (Support.Microsoft.FStar.Util.format3 "forall %s.{:pattern %s} %s" _70_19979 _70_19978 _70_19977))))
end
| QExists ((bs, pats, t)) -> begin
(let _70_19982 = (to_string_l " " binder_to_string bs)
in (let _70_19981 = (to_string_l "; " term_to_string pats)
in (let _70_19980 = (Support.All.pipe_right t term_to_string)
in (Support.Microsoft.FStar.Util.format3 "exists %s.{:pattern %s} %s" _70_19982 _70_19981 _70_19980))))
end
| Refine ((b, t)) -> begin
(let _70_19984 = (Support.All.pipe_right b binder_to_string)
in (let _70_19983 = (Support.All.pipe_right t term_to_string)
in (Support.Microsoft.FStar.Util.format2 "%s:{%s}" _70_19984 _70_19983)))
end
| NamedTyp ((x, t)) -> begin
(let _70_19985 = (Support.All.pipe_right t term_to_string)
in (Support.Microsoft.FStar.Util.format2 "%s:%s" x.Microsoft_FStar_Absyn_Syntax.idText _70_19985))
end
| Paren (t) -> begin
(let _70_19986 = (Support.All.pipe_right t term_to_string)
in (Support.Microsoft.FStar.Util.format1 "(%s)" _70_19986))
end
| Product ((bs, t)) -> begin
(let _70_19989 = (let _70_19987 = (Support.All.pipe_right bs (Support.List.map binder_to_string))
in (Support.All.pipe_right _70_19987 (Support.String.concat ",")))
in (let _70_19988 = (Support.All.pipe_right t term_to_string)
in (Support.Microsoft.FStar.Util.format2 "Unidentified product: [%s] %s" _70_19989 _70_19988)))
end
| t -> begin
(Support.All.failwith "Missing case in term_to_string")
end))
and binder_to_string = (fun ( x ) -> (let s = (match (x.b) with
| Variable (i) -> begin
i.Microsoft_FStar_Absyn_Syntax.idText
end
| TVariable (i) -> begin
(Support.Microsoft.FStar.Util.format1 "%s:_" i.Microsoft_FStar_Absyn_Syntax.idText)
end
| (TAnnotated ((i, t))) | (Annotated ((i, t))) -> begin
(let _70_19991 = (Support.All.pipe_right t term_to_string)
in (Support.Microsoft.FStar.Util.format2 "%s:%s" i.Microsoft_FStar_Absyn_Syntax.idText _70_19991))
end
| NoName (t) -> begin
(Support.All.pipe_right t term_to_string)
end)
in (match (x.aqual) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
(Support.Microsoft.FStar.Util.format1 "#%s" s)
end
| Some (Microsoft_FStar_Absyn_Syntax.Equality) -> begin
(Support.Microsoft.FStar.Util.format1 "=%s" s)
end
| _39_425 -> begin
s
end)))
and pat_to_string = (fun ( x ) -> (match (x.pat) with
| PatWild -> begin
"_"
end
| PatConst (c) -> begin
(Microsoft_FStar_Absyn_Print.const_to_string c)
end
| PatApp ((p, ps)) -> begin
(let _70_19994 = (Support.All.pipe_right p pat_to_string)
in (let _70_19993 = (to_string_l " " pat_to_string ps)
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _70_19994 _70_19993)))
end
| (PatTvar ((i, true))) | (PatVar ((i, true))) -> begin
(Support.Microsoft.FStar.Util.format1 "#%s" i.Microsoft_FStar_Absyn_Syntax.idText)
end
| (PatTvar ((i, false))) | (PatVar ((i, false))) -> begin
i.Microsoft_FStar_Absyn_Syntax.idText
end
| PatName (l) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end
| PatList (l) -> begin
(let _70_19995 = (to_string_l "; " pat_to_string l)
in (Support.Microsoft.FStar.Util.format1 "[%s]" _70_19995))
end
| PatTuple ((l, false)) -> begin
(let _70_19996 = (to_string_l ", " pat_to_string l)
in (Support.Microsoft.FStar.Util.format1 "(%s)" _70_19996))
end
| PatTuple ((l, true)) -> begin
(let _70_19997 = (to_string_l ", " pat_to_string l)
in (Support.Microsoft.FStar.Util.format1 "(|%s|)" _70_19997))
end
| PatRecord (l) -> begin
(let _70_20001 = (to_string_l "; " (fun ( _39_464 ) -> (match (_39_464) with
| (f, e) -> begin
(let _70_20000 = (Microsoft_FStar_Absyn_Print.sli f)
in (let _70_19999 = (Support.All.pipe_right e pat_to_string)
in (Support.Microsoft.FStar.Util.format2 "%s=%s" _70_20000 _70_19999)))
end)) l)
in (Support.Microsoft.FStar.Util.format1 "{%s}" _70_20001))
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatAscribed ((p, t)) -> begin
(let _70_20003 = (Support.All.pipe_right p pat_to_string)
in (let _70_20002 = (Support.All.pipe_right t term_to_string)
in (Support.Microsoft.FStar.Util.format2 "(%s:%s)" _70_20003 _70_20002)))
end))

let error = (fun ( msg ) ( tm ) ( r ) -> (let tm = (Support.All.pipe_right tm term_to_string)
in (let tm = (match (((Support.String.length tm) >= 80)) with
| true -> begin
(let _70_20007 = (Support.Microsoft.FStar.Util.substring tm 0 77)
in (Support.String.strcat _70_20007 "..."))
end
| false -> begin
tm
end)
in (raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat (Support.String.strcat msg "\n") tm), r)))))))

let consPat = (fun ( r ) ( hd ) ( tl ) -> PatApp (((mk_pattern (PatName (Microsoft_FStar_Absyn_Const.cons_lid)) r), (hd)::(tl)::[])))

let consTerm = (fun ( r ) ( hd ) ( tl ) -> (mk_term (Construct ((Microsoft_FStar_Absyn_Const.cons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))

let lexConsTerm = (fun ( r ) ( hd ) ( tl ) -> (mk_term (Construct ((Microsoft_FStar_Absyn_Const.lexcons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))

let mkConsList = (fun ( r ) ( elts ) -> (let nil = (mk_term (Construct ((Microsoft_FStar_Absyn_Const.nil_lid, []))) r Expr)
in (Support.List.fold_right (fun ( e ) ( tl ) -> (consTerm r e tl)) elts nil)))

let mkLexList = (fun ( r ) ( elts ) -> (let nil = (mk_term (Construct ((Microsoft_FStar_Absyn_Const.lextop_lid, []))) r Expr)
in (Support.List.fold_right (fun ( e ) ( tl ) -> (lexConsTerm r e tl)) elts nil)))

let mkApp = (fun ( t ) ( args ) ( r ) -> (match (args) with
| [] -> begin
t
end
| _39_500 -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct ((s, args))) r Un)
end
| _39_504 -> begin
(Support.List.fold_left (fun ( t ) ( _39_508 ) -> (match (_39_508) with
| (a, imp) -> begin
(mk_term (App ((t, a, imp))) r Un)
end)) t args)
end)
end))

let mkRefSet = (fun ( r ) ( elts ) -> (let empty = (let _70_20051 = (let _70_20050 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.set_empty r)
in Var (_70_20050))
in (mk_term _70_20051 r Expr))
in (let ref_constr = (let _70_20053 = (let _70_20052 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.heap_ref r)
in Var (_70_20052))
in (mk_term _70_20053 r Expr))
in (let singleton = (let _70_20055 = (let _70_20054 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.set_singleton r)
in Var (_70_20054))
in (mk_term _70_20055 r Expr))
in (let union = (let _70_20057 = (let _70_20056 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.set_union r)
in Var (_70_20056))
in (mk_term _70_20057 r Expr))
in (Support.List.fold_right (fun ( e ) ( tl ) -> (let e = (mkApp ref_constr (((e, Nothing))::[]) r)
in (let single_e = (mkApp singleton (((e, Nothing))::[]) r)
in (mkApp union (((single_e, Nothing))::((tl, Nothing))::[]) r)))) elts empty))))))

let mkExplicitApp = (fun ( t ) ( args ) ( r ) -> (match (args) with
| [] -> begin
t
end
| _39_524 -> begin
(match (t.tm) with
| Name (s) -> begin
(let _70_20069 = (let _70_20068 = (let _70_20067 = (Support.List.map (fun ( a ) -> (a, Nothing)) args)
in (s, _70_20067))
in Construct (_70_20068))
in (mk_term _70_20069 r Un))
end
| _39_529 -> begin
(Support.List.fold_left (fun ( t ) ( a ) -> (mk_term (App ((t, a, Nothing))) r Un)) t args)
end)
end))

let mkAdmitMagic = (fun ( r ) -> (let unit_const = (mk_term (Const (Microsoft_FStar_Absyn_Syntax.Const_unit)) r Expr)
in (let admit = (let admit_name = (let _70_20075 = (let _70_20074 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.admit_lid r)
in Var (_70_20074))
in (mk_term _70_20075 r Expr))
in (mkExplicitApp admit_name ((unit_const)::[]) r))
in (let magic = (let magic_name = (let _70_20077 = (let _70_20076 = (Microsoft_FStar_Absyn_Util.set_lid_range Microsoft_FStar_Absyn_Const.magic_lid r)
in Var (_70_20076))
in (mk_term _70_20077 r Expr))
in (mkExplicitApp magic_name ((unit_const)::[]) r))
in (let admit_magic = (mk_term (Seq ((admit, magic))) r Expr)
in admit_magic)))))

let mkWildAdmitMagic = (fun ( r ) -> (let _70_20079 = (mkAdmitMagic r)
in ((mk_pattern PatWild r), None, _70_20079)))

let focusBranches = (fun ( branches ) ( r ) -> (let should_filter = (Support.Microsoft.FStar.Util.for_some Support.Prims.fst branches)
in (match (should_filter) with
| true -> begin
(let _39_543 = (Microsoft_FStar_Tc_Errors.warn r "Focusing on only some cases")
in (let focussed = (let _70_20082 = (Support.List.filter Support.Prims.fst branches)
in (Support.All.pipe_right _70_20082 (Support.List.map Support.Prims.snd)))
in (let _70_20084 = (let _70_20083 = (mkWildAdmitMagic r)
in (_70_20083)::[])
in (Support.List.append focussed _70_20084))))
end
| false -> begin
(Support.All.pipe_right branches (Support.List.map Support.Prims.snd))
end)))

let focusLetBindings = (fun ( lbs ) ( r ) -> (let should_filter = (Support.Microsoft.FStar.Util.for_some Support.Prims.fst lbs)
in (match (should_filter) with
| true -> begin
(let _39_549 = (Microsoft_FStar_Tc_Errors.warn r "Focusing on only some cases in this (mutually) recursive definition")
in (Support.List.map (fun ( _39_553 ) -> (match (_39_553) with
| (f, lb) -> begin
(match (f) with
| true -> begin
lb
end
| false -> begin
(let _70_20088 = (mkAdmitMagic r)
in ((Support.Prims.fst lb), _70_20088))
end)
end)) lbs))
end
| false -> begin
(Support.All.pipe_right lbs (Support.List.map Support.Prims.snd))
end)))

let mkFsTypApp = (fun ( t ) ( args ) ( r ) -> (let _70_20096 = (Support.List.map (fun ( a ) -> (a, FsTypApp)) args)
in (mkApp t _70_20096 r)))

let mkTuple = (fun ( args ) ( r ) -> (let cons = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid (Support.List.length args) r)
in (let _70_20102 = (Support.List.map (fun ( x ) -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _70_20102 r))))

let mkDTuple = (fun ( args ) ( r ) -> (let cons = (Microsoft_FStar_Absyn_Util.mk_dtuple_data_lid (Support.List.length args) r)
in (let _70_20108 = (Support.List.map (fun ( x ) -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _70_20108 r))))

let mkRefinedBinder = (fun ( id ) ( t ) ( refopt ) ( m ) ( implicit ) -> (let b = (mk_binder (Annotated ((id, t))) m Type implicit)
in (match (refopt) with
| None -> begin
b
end
| Some (t) -> begin
(mk_binder (Annotated ((id, (mk_term (Refine ((b, t))) m Type)))) m Type implicit)
end)))

let rec extract_named_refinement = (fun ( t1 ) -> (match (t1.tm) with
| NamedTyp ((x, t)) -> begin
Some ((x, t, None))
end
| Refine (({b = Annotated ((x, t)); brange = _39_585; blevel = _39_583; aqual = _39_581}, t')) -> begin
Some ((x, t, Some (t')))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| _39_597 -> begin
None
end))




