
type level =
| Un
| Expr
| Type
| Kind
| Formula

type lid =
Microsoft_FStar_Absyn_Syntax.l__LongIdent

type imp =
| FsTypApp
| Hash
| Nothing

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
| Labeled of (term * string * bool) and term =
{tm : term'; range : Support.Microsoft.FStar.Range.range; level : level} and binder' =
| Variable of Microsoft_FStar_Absyn_Syntax.ident
| TVariable of Microsoft_FStar_Absyn_Syntax.ident
| Annotated of (Microsoft_FStar_Absyn_Syntax.ident * term)
| TAnnotated of (Microsoft_FStar_Absyn_Syntax.ident * term)
| NoName of term and binder =
{b : binder'; brange : Support.Microsoft.FStar.Range.range; blevel : level; aqual : Microsoft_FStar_Absyn_Syntax.aqual} and pattern' =
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
| PatOr of pattern list and pattern =
{pat : pattern'; prange : Support.Microsoft.FStar.Range.range} and branch =
(pattern * term option * term)

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

type qualifiers =
Microsoft_FStar_Absyn_Syntax.qualifier list

type lift =
{msource : lid; mdest : lid; lift_op : term}

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
| Pragma of Microsoft_FStar_Absyn_Syntax.pragma and decl =
{d : decl'; drange : Support.Microsoft.FStar.Range.range} and effect_decl =
| DefineEffect of (Microsoft_FStar_Absyn_Syntax.ident * binder list * term * decl list)
| RedefineEffect of (Microsoft_FStar_Absyn_Syntax.ident * binder list * term)

type modul =
| Module of (Microsoft_FStar_Absyn_Syntax.l__LongIdent * decl list)
| Interface of (Microsoft_FStar_Absyn_Syntax.l__LongIdent * decl list * bool)

type file =
modul list

type inputFragment =
(file, decl list) Support.Microsoft.FStar.Util.either

let mk_decl = (fun d r -> {d = d; drange = r})

let mk_binder = (fun b r l i -> {b = b; brange = r; blevel = l; aqual = i})

let mk_term = (fun t r l -> {tm = t; range = r; level = l})

let mk_pattern = (fun p r -> {pat = p; prange = r})

let un_curry_abs = (fun ps body -> (match (body.tm) with
| Abs ((p', body')) -> begin
Abs (((Support.List.append ps p'), body'))
end
| _ -> begin
Abs ((ps, body))
end))

let mk_function = (fun branches r1 r2 -> (let x = (Microsoft_FStar_Absyn_Util.genident (Some (r1)))
in (mk_term (Abs ((((mk_pattern (PatVar ((x, false))) r1))::[], (mk_term (Match (((mk_term (Var ((Microsoft_FStar_Absyn_Syntax.lid_of_ids ((x)::[])))) r1 Expr), branches))) r2 Expr)))) r2 Expr)))

let un_function = (fun p tm -> (match ((p.pat, tm.tm)) with
| (PatVar (_), Abs ((pats, body))) -> begin
Some (((mk_pattern (PatApp ((p, pats))) p.prange), body))
end
| _ -> begin
None
end))

let lid_with_range = (fun lid r -> (Microsoft_FStar_Absyn_Syntax.lid_of_path (Microsoft_FStar_Absyn_Syntax.path_of_lid lid) r))

let to_string_l = (fun sep f l -> (Support.String.concat sep (Support.List.map f l)))

let imp_to_string = (fun _111790 -> (match (_111790) with
| Hash -> begin
"#"
end
| _ -> begin
""
end))

let rec term_to_string = (fun x -> (match (x.tm) with
| Wild -> begin
"\x5f"
end
| Requires ((t, _)) -> begin
(Support.Microsoft.FStar.Util.format1 "\x28requires %s\x29" (term_to_string t))
end
| Ensures ((t, _)) -> begin
(Support.Microsoft.FStar.Util.format1 "\x28ensures %s\x29" (term_to_string t))
end
| Labeled ((t, l, _)) -> begin
(Support.Microsoft.FStar.Util.format2 "\x28labeled %s %s\x29" l (term_to_string t))
end
| Const (c) -> begin
(Microsoft_FStar_Absyn_Print.const_to_string c)
end
| Op ((s, xs)) -> begin
(Support.Microsoft.FStar.Util.format2 "%s\x28%s\x29" s (Support.String.concat ", " (Support.List.map (fun x -> (term_to_string x)) xs)))
end
| Tvar (id) -> begin
id.Microsoft_FStar_Absyn_Syntax.idText
end
| (Var (l)) | (Name (l)) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end
| Construct ((l, args)) -> begin
(Support.Microsoft.FStar.Util.format2 "\x28%s %s\x29" (Microsoft_FStar_Absyn_Print.sli l) (to_string_l " " (fun _112010 -> (match (_112010) with
| (a, imp) -> begin
(Support.Microsoft.FStar.Util.format2 "%s%s" (imp_to_string imp) (term_to_string a))
end)) args))
end
| Abs ((pats, t)) when (x.level = Expr) -> begin
(Support.Microsoft.FStar.Util.format2 "\x28fun %s -> %s\x29" (to_string_l " " pat_to_string pats) (term_to_string t))
end
| Abs ((pats, t)) when (x.level = Type) -> begin
(Support.Microsoft.FStar.Util.format2 "\x28fun %s => %s\x29" (to_string_l " " pat_to_string pats) (term_to_string t))
end
| App ((t1, t2, imp)) -> begin
(Support.Microsoft.FStar.Util.format3 "%s %s%s" (term_to_string t1) (imp_to_string imp) (term_to_string t2))
end
| Let ((false, (pat, tm)::[], body)) -> begin
(Support.Microsoft.FStar.Util.format3 "let %s = %s in %s" (pat_to_string pat) (term_to_string tm) (term_to_string body))
end
| Let ((_, lbs, body)) -> begin
(Support.Microsoft.FStar.Util.format2 "let rec %s in %s" (to_string_l " and " (fun _112040 -> (match (_112040) with
| (p, b) -> begin
(Support.Microsoft.FStar.Util.format2 "%s=%s" (pat_to_string p) (term_to_string b))
end)) lbs) (term_to_string body))
end
| Seq ((t1, t2)) -> begin
(Support.Microsoft.FStar.Util.format2 "%s; %s" (term_to_string t1) (term_to_string t2))
end
| If ((t1, t2, t3)) -> begin
(Support.Microsoft.FStar.Util.format3 "if %s then %s else %s" (term_to_string t1) (term_to_string t2) (term_to_string t3))
end
| Match ((t, branches)) -> begin
(Support.Microsoft.FStar.Util.format2 "match %s with %s" (term_to_string t) (to_string_l " | " (fun _112057 -> (match (_112057) with
| (p, w, e) -> begin
(Support.Microsoft.FStar.Util.format3 "%s %s -> %s" (pat_to_string p) (match (w) with
| None -> begin
""
end
| Some (e) -> begin
(Support.Microsoft.FStar.Util.format1 "when %s" (term_to_string e))
end) (term_to_string e))
end)) branches))
end
| Ascribed ((t1, t2)) -> begin
(Support.Microsoft.FStar.Util.format2 "\x28%s : %s\x29" (term_to_string t1) (term_to_string t2))
end
| Record ((Some (e), fields)) -> begin
(Support.Microsoft.FStar.Util.format2 "\x7b%s with %s\x7d" (term_to_string e) (to_string_l " " (fun _112072 -> (match (_112072) with
| (l, e) -> begin
(Support.Microsoft.FStar.Util.format2 "%s=%s" (Microsoft_FStar_Absyn_Print.sli l) (term_to_string e))
end)) fields))
end
| Record ((None, fields)) -> begin
(Support.Microsoft.FStar.Util.format1 "\x7b%s\x7d" (to_string_l " " (fun _112079 -> (match (_112079) with
| (l, e) -> begin
(Support.Microsoft.FStar.Util.format2 "%s=%s" (Microsoft_FStar_Absyn_Print.sli l) (term_to_string e))
end)) fields))
end
| Project ((e, l)) -> begin
(Support.Microsoft.FStar.Util.format2 "%s.%s" (term_to_string e) (Microsoft_FStar_Absyn_Print.sli l))
end
| Product (([], t)) -> begin
(term_to_string t)
end
| Product ((b::hd::tl, t)) -> begin
(term_to_string (mk_term (Product (((b)::[], (mk_term (Product (((hd)::tl, t))) x.range x.level)))) x.range x.level))
end
| Product ((b::[], t)) when (x.level = Type) -> begin
(Support.Microsoft.FStar.Util.format2 "%s -> %s" (binder_to_string b) (term_to_string t))
end
| Product ((b::[], t)) when (x.level = Kind) -> begin
(Support.Microsoft.FStar.Util.format2 "%s => %s" (binder_to_string b) (term_to_string t))
end
| Sum ((binders, t)) -> begin
(Support.Microsoft.FStar.Util.format2 "%s * %s" ((Support.String.concat " * ") ((Support.List.map binder_to_string) binders)) (term_to_string t))
end
| QForall ((bs, pats, t)) -> begin
(Support.Microsoft.FStar.Util.format3 "forall %s.\x7b:pattern %s\x7d %s" (to_string_l " " binder_to_string bs) (to_string_l "; " term_to_string pats) (term_to_string t))
end
| QExists ((bs, pats, t)) -> begin
(Support.Microsoft.FStar.Util.format3 "exists %s.\x7b:pattern %s\x7d %s" (to_string_l " " binder_to_string bs) (to_string_l "; " term_to_string pats) (term_to_string t))
end
| Refine ((b, t)) -> begin
(Support.Microsoft.FStar.Util.format2 "%s:\x7b%s\x7d" (binder_to_string b) (term_to_string t))
end
| NamedTyp ((x, t)) -> begin
(Support.Microsoft.FStar.Util.format2 "%s:%s" x.Microsoft_FStar_Absyn_Syntax.idText (term_to_string t))
end
| Paren (t) -> begin
(Support.Microsoft.FStar.Util.format1 "\x28%s\x29" (term_to_string t))
end
| Product ((bs, t)) -> begin
(Support.Microsoft.FStar.Util.format2 "Unidentified product: \x5b%s\x5d %s" ((Support.String.concat ",") ((Support.List.map binder_to_string) bs)) (term_to_string t))
end
| t -> begin
(failwith ("Missing case in term\x5fto\x5fstring"))
end))
and binder_to_string = (fun x -> (let s = (match (x.b) with
| Variable (i) -> begin
i.Microsoft_FStar_Absyn_Syntax.idText
end
| TVariable (i) -> begin
(Support.Microsoft.FStar.Util.format1 "%s:\x5f" i.Microsoft_FStar_Absyn_Syntax.idText)
end
| (TAnnotated ((i, t))) | (Annotated ((i, t))) -> begin
(Support.Microsoft.FStar.Util.format2 "%s:%s" i.Microsoft_FStar_Absyn_Syntax.idText (term_to_string t))
end
| NoName (t) -> begin
(term_to_string t)
end)
in (match (x.aqual) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
(Support.Microsoft.FStar.Util.format1 "#%s" s)
end
| Some (Microsoft_FStar_Absyn_Syntax.Equality) -> begin
(Support.Microsoft.FStar.Util.format1 "=%s" s)
end
| _ -> begin
s
end)))
and pat_to_string = (fun x -> (match (x.pat) with
| PatWild -> begin
"\x5f"
end
| PatConst (c) -> begin
(Microsoft_FStar_Absyn_Print.const_to_string c)
end
| PatApp ((p, ps)) -> begin
(Support.Microsoft.FStar.Util.format2 "\x28%s %s\x29" (pat_to_string p) (to_string_l " " pat_to_string ps))
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
(Support.Microsoft.FStar.Util.format1 "\x5b%s\x5d" (to_string_l "; " pat_to_string l))
end
| PatTuple ((l, false)) -> begin
(Support.Microsoft.FStar.Util.format1 "\x28%s\x29" (to_string_l ", " pat_to_string l))
end
| PatTuple ((l, true)) -> begin
(Support.Microsoft.FStar.Util.format1 "\x28|%s|\x29" (to_string_l ", " pat_to_string l))
end
| PatRecord (l) -> begin
(Support.Microsoft.FStar.Util.format1 "\x7b%s\x7d" (to_string_l "; " (fun _112193 -> (match (_112193) with
| (f, e) -> begin
(Support.Microsoft.FStar.Util.format2 "%s=%s" (Microsoft_FStar_Absyn_Print.sli f) (pat_to_string e))
end)) l))
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatAscribed ((p, t)) -> begin
(Support.Microsoft.FStar.Util.format2 "\x28%s:%s\x29" (pat_to_string p) (term_to_string t))
end))

let error = (fun msg tm r -> (let tm = (term_to_string tm)
in (let tm = if ((Support.String.length tm) >= 80) then begin
(Support.String.strcat (Support.Microsoft.FStar.Util.substring tm 0 77) "...")
end else begin
tm
end
in (raise (Microsoft_FStar_Absyn_Syntax.Error (((Support.String.strcat (Support.String.strcat msg "\n") tm), r)))))))

let consPat = (fun r hd tl -> PatApp (((mk_pattern (PatName (Microsoft_FStar_Absyn_Const.cons_lid)) r), (hd)::(tl)::[])))

let consTerm = (fun r hd tl -> (mk_term (Construct ((Microsoft_FStar_Absyn_Const.cons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))

let lexConsTerm = (fun r hd tl -> (mk_term (Construct ((Microsoft_FStar_Absyn_Const.lexcons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))

let mkConsList = (fun r elts -> (let nil = (mk_term (Construct ((Microsoft_FStar_Absyn_Const.nil_lid, []))) r Expr)
in (Support.List.fold_right (fun e tl -> (consTerm r e tl)) elts nil)))

let mkLexList = (fun r elts -> (let nil = (mk_term (Construct ((Microsoft_FStar_Absyn_Const.lextop_lid, []))) r Expr)
in (Support.List.fold_right (fun e tl -> (lexConsTerm r e tl)) elts nil)))

let mkApp = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _ -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct ((s, args))) r Un)
end
| _ -> begin
(Support.List.fold_left (fun t _112237 -> (match (_112237) with
| (a, imp) -> begin
(mk_term (App ((t, a, imp))) r Un)
end)) t args)
end)
end))

let mkExplicitApp = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _ -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct ((s, (Support.List.map (fun a -> (a, Nothing)) args)))) r Un)
end
| _ -> begin
(Support.List.fold_left (fun t a -> (mk_term (App ((t, a, Nothing))) r Un)) t args)
end)
end))

let mkFsTypApp = (fun t args r -> (mkApp t (Support.List.map (fun a -> (a, FsTypApp)) args) r))

let mkTuple = (fun args r -> (let cons = (Microsoft_FStar_Absyn_Util.mk_tuple_data_lid (Support.List.length args) r)
in (mkApp (mk_term (Name (cons)) r Expr) (Support.List.map (fun x -> (x, Nothing)) args) r)))

let mkDTuple = (fun args r -> (let cons = (Microsoft_FStar_Absyn_Util.mk_dtuple_data_lid (Support.List.length args) r)
in (mkApp (mk_term (Name (cons)) r Expr) (Support.List.map (fun x -> (x, Nothing)) args) r)))

let mkRefinedBinder = (fun id t refopt m implicit -> (let b = (mk_binder (Annotated ((id, t))) m Type implicit)
in (match (refopt) with
| None -> begin
b
end
| Some (t) -> begin
(mk_binder (Annotated ((id, (mk_term (Refine ((b, t))) m Type)))) m Type implicit)
end)))

let rec extract_named_refinement = (fun t1 -> (match (t1.tm) with
| NamedTyp ((x, t)) -> begin
Some ((x, t, None))
end
| Refine (({b = Annotated ((x, t)); brange = _; blevel = _; aqual = _}, t')) -> begin
Some ((x, t, Some (t')))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| _ -> begin
None
end))




