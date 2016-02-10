
open Prims
# 28 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type level =
| Un
| Expr
| Type
| Kind
| Formula

# 34 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Un = (fun _discr_ -> (match (_discr_) with
| Un (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Expr = (fun _discr_ -> (match (_discr_) with
| Expr (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Type = (fun _discr_ -> (match (_discr_) with
| Type (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Kind = (fun _discr_ -> (match (_discr_) with
| Kind (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Formula = (fun _discr_ -> (match (_discr_) with
| Formula (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type imp =
| FsTypApp
| Hash
| Nothing

# 36 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_FsTypApp = (fun _discr_ -> (match (_discr_) with
| FsTypApp (_) -> begin
true
end
| _ -> begin
false
end))

# 37 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Hash = (fun _discr_ -> (match (_discr_) with
| Hash (_) -> begin
true
end
| _ -> begin
false
end))

# 38 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Nothing = (fun _discr_ -> (match (_discr_) with
| Nothing (_) -> begin
true
end
| _ -> begin
false
end))

# 38 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type arg_qualifier =
| Implicit
| Equality

# 40 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Implicit = (fun _discr_ -> (match (_discr_) with
| Implicit (_) -> begin
true
end
| _ -> begin
false
end))

# 41 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Equality = (fun _discr_ -> (match (_discr_) with
| Equality (_) -> begin
true
end
| _ -> begin
false
end))

# 41 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type aqual =
arg_qualifier Prims.option

# 42 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type term' =
| Wild
| Const of FStar_Const.sconst
| Op of (Prims.string * term Prims.list)
| Tvar of FStar_Ident.ident
| Var of FStar_Ident.lid
| Name of FStar_Ident.lid
| Construct of (FStar_Ident.lid * (term * imp) Prims.list)
| Abs of (pattern Prims.list * term)
| App of (term * term * imp)
| Let of (Prims.bool * (pattern * term) Prims.list * term)
| Seq of (term * term)
| If of (term * term * term)
| Match of (term * branch Prims.list)
| TryWith of (term * branch Prims.list)
| Ascribed of (term * term)
| Record of (term Prims.option * (FStar_Ident.lid * term) Prims.list)
| Project of (term * FStar_Ident.lid)
| Product of (binder Prims.list * term)
| Sum of (binder Prims.list * term)
| QForall of (binder Prims.list * term Prims.list Prims.list * term)
| QExists of (binder Prims.list * term Prims.list Prims.list * term)
| Refine of (binder * term)
| NamedTyp of (FStar_Ident.ident * term)
| Paren of term
| Requires of (term * Prims.string Prims.option)
| Ensures of (term * Prims.string Prims.option)
| Labeled of (term * Prims.string * Prims.bool) 
 and term =
{tm : term'; range : FStar_Range.range; level : level} 
 and binder' =
| Variable of FStar_Ident.ident
| TVariable of FStar_Ident.ident
| Annotated of (FStar_Ident.ident * term)
| TAnnotated of (FStar_Ident.ident * term)
| NoName of term 
 and binder =
{b : binder'; brange : FStar_Range.range; blevel : level; aqual : aqual} 
 and pattern' =
| PatWild
| PatConst of FStar_Const.sconst
| PatApp of (pattern * pattern Prims.list)
| PatVar of (FStar_Ident.ident * Prims.bool)
| PatName of FStar_Ident.lid
| PatTvar of (FStar_Ident.ident * Prims.bool)
| PatList of pattern Prims.list
| PatTuple of (pattern Prims.list * Prims.bool)
| PatRecord of (FStar_Ident.lid * pattern) Prims.list
| PatAscribed of (pattern * term)
| PatOr of pattern Prims.list 
 and pattern =
{pat : pattern'; prange : FStar_Range.range} 
 and branch =
(pattern * term Prims.option * term)

# 45 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Wild = (fun _discr_ -> (match (_discr_) with
| Wild (_) -> begin
true
end
| _ -> begin
false
end))

# 46 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Const = (fun _discr_ -> (match (_discr_) with
| Const (_) -> begin
true
end
| _ -> begin
false
end))

# 47 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Op = (fun _discr_ -> (match (_discr_) with
| Op (_) -> begin
true
end
| _ -> begin
false
end))

# 48 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Tvar = (fun _discr_ -> (match (_discr_) with
| Tvar (_) -> begin
true
end
| _ -> begin
false
end))

# 49 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Var = (fun _discr_ -> (match (_discr_) with
| Var (_) -> begin
true
end
| _ -> begin
false
end))

# 50 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Name = (fun _discr_ -> (match (_discr_) with
| Name (_) -> begin
true
end
| _ -> begin
false
end))

# 51 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Construct = (fun _discr_ -> (match (_discr_) with
| Construct (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Abs = (fun _discr_ -> (match (_discr_) with
| Abs (_) -> begin
true
end
| _ -> begin
false
end))

# 53 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Let = (fun _discr_ -> (match (_discr_) with
| Let (_) -> begin
true
end
| _ -> begin
false
end))

# 55 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Seq = (fun _discr_ -> (match (_discr_) with
| Seq (_) -> begin
true
end
| _ -> begin
false
end))

# 56 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_If = (fun _discr_ -> (match (_discr_) with
| If (_) -> begin
true
end
| _ -> begin
false
end))

# 57 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Match = (fun _discr_ -> (match (_discr_) with
| Match (_) -> begin
true
end
| _ -> begin
false
end))

# 58 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_TryWith = (fun _discr_ -> (match (_discr_) with
| TryWith (_) -> begin
true
end
| _ -> begin
false
end))

# 59 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Ascribed = (fun _discr_ -> (match (_discr_) with
| Ascribed (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Record = (fun _discr_ -> (match (_discr_) with
| Record (_) -> begin
true
end
| _ -> begin
false
end))

# 61 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Project = (fun _discr_ -> (match (_discr_) with
| Project (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Product = (fun _discr_ -> (match (_discr_) with
| Product (_) -> begin
true
end
| _ -> begin
false
end))

# 63 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Sum = (fun _discr_ -> (match (_discr_) with
| Sum (_) -> begin
true
end
| _ -> begin
false
end))

# 64 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_QForall = (fun _discr_ -> (match (_discr_) with
| QForall (_) -> begin
true
end
| _ -> begin
false
end))

# 65 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_QExists = (fun _discr_ -> (match (_discr_) with
| QExists (_) -> begin
true
end
| _ -> begin
false
end))

# 66 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Refine = (fun _discr_ -> (match (_discr_) with
| Refine (_) -> begin
true
end
| _ -> begin
false
end))

# 67 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_NamedTyp = (fun _discr_ -> (match (_discr_) with
| NamedTyp (_) -> begin
true
end
| _ -> begin
false
end))

# 68 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Paren = (fun _discr_ -> (match (_discr_) with
| Paren (_) -> begin
true
end
| _ -> begin
false
end))

# 69 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Requires = (fun _discr_ -> (match (_discr_) with
| Requires (_) -> begin
true
end
| _ -> begin
false
end))

# 70 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Ensures = (fun _discr_ -> (match (_discr_) with
| Ensures (_) -> begin
true
end
| _ -> begin
false
end))

# 71 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Labeled = (fun _discr_ -> (match (_discr_) with
| Labeled (_) -> begin
true
end
| _ -> begin
false
end))

# 73 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Mkterm : term  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkterm"))))

# 76 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Variable = (fun _discr_ -> (match (_discr_) with
| Variable (_) -> begin
true
end
| _ -> begin
false
end))

# 77 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_TVariable = (fun _discr_ -> (match (_discr_) with
| TVariable (_) -> begin
true
end
| _ -> begin
false
end))

# 78 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Annotated = (fun _discr_ -> (match (_discr_) with
| Annotated (_) -> begin
true
end
| _ -> begin
false
end))

# 79 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_TAnnotated = (fun _discr_ -> (match (_discr_) with
| TAnnotated (_) -> begin
true
end
| _ -> begin
false
end))

# 80 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_NoName = (fun _discr_ -> (match (_discr_) with
| NoName (_) -> begin
true
end
| _ -> begin
false
end))

# 81 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Mkbinder : binder  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbinder"))))

# 84 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_PatWild = (fun _discr_ -> (match (_discr_) with
| PatWild (_) -> begin
true
end
| _ -> begin
false
end))

# 85 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_PatConst = (fun _discr_ -> (match (_discr_) with
| PatConst (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_PatApp = (fun _discr_ -> (match (_discr_) with
| PatApp (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_PatVar = (fun _discr_ -> (match (_discr_) with
| PatVar (_) -> begin
true
end
| _ -> begin
false
end))

# 88 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_PatName = (fun _discr_ -> (match (_discr_) with
| PatName (_) -> begin
true
end
| _ -> begin
false
end))

# 89 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_PatTvar = (fun _discr_ -> (match (_discr_) with
| PatTvar (_) -> begin
true
end
| _ -> begin
false
end))

# 90 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_PatList = (fun _discr_ -> (match (_discr_) with
| PatList (_) -> begin
true
end
| _ -> begin
false
end))

# 91 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_PatTuple = (fun _discr_ -> (match (_discr_) with
| PatTuple (_) -> begin
true
end
| _ -> begin
false
end))

# 92 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_PatRecord = (fun _discr_ -> (match (_discr_) with
| PatRecord (_) -> begin
true
end
| _ -> begin
false
end))

# 93 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_PatAscribed = (fun _discr_ -> (match (_discr_) with
| PatAscribed (_) -> begin
true
end
| _ -> begin
false
end))

# 94 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_PatOr = (fun _discr_ -> (match (_discr_) with
| PatOr (_) -> begin
true
end
| _ -> begin
false
end))

# 95 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))

# 46 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Const____0 : term'  ->  FStar_Const.sconst = (fun projectee -> (match (projectee) with
| Const (_59_13) -> begin
_59_13
end))

# 47 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Op____0 : term'  ->  (Prims.string * term Prims.list) = (fun projectee -> (match (projectee) with
| Op (_59_16) -> begin
_59_16
end))

# 48 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Tvar____0 : term'  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| Tvar (_59_19) -> begin
_59_19
end))

# 49 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Var____0 : term'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Var (_59_22) -> begin
_59_22
end))

# 50 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Name____0 : term'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Name (_59_25) -> begin
_59_25
end))

# 51 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Construct____0 : term'  ->  (FStar_Ident.lid * (term * imp) Prims.list) = (fun projectee -> (match (projectee) with
| Construct (_59_28) -> begin
_59_28
end))

# 52 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Abs____0 : term'  ->  (pattern Prims.list * term) = (fun projectee -> (match (projectee) with
| Abs (_59_31) -> begin
_59_31
end))

# 53 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___App____0 : term'  ->  (term * term * imp) = (fun projectee -> (match (projectee) with
| App (_59_34) -> begin
_59_34
end))

# 54 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Let____0 : term'  ->  (Prims.bool * (pattern * term) Prims.list * term) = (fun projectee -> (match (projectee) with
| Let (_59_37) -> begin
_59_37
end))

# 55 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Seq____0 : term'  ->  (term * term) = (fun projectee -> (match (projectee) with
| Seq (_59_40) -> begin
_59_40
end))

# 56 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___If____0 : term'  ->  (term * term * term) = (fun projectee -> (match (projectee) with
| If (_59_43) -> begin
_59_43
end))

# 57 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Match____0 : term'  ->  (term * branch Prims.list) = (fun projectee -> (match (projectee) with
| Match (_59_46) -> begin
_59_46
end))

# 58 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___TryWith____0 : term'  ->  (term * branch Prims.list) = (fun projectee -> (match (projectee) with
| TryWith (_59_49) -> begin
_59_49
end))

# 59 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Ascribed____0 : term'  ->  (term * term) = (fun projectee -> (match (projectee) with
| Ascribed (_59_52) -> begin
_59_52
end))

# 60 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Record____0 : term'  ->  (term Prims.option * (FStar_Ident.lid * term) Prims.list) = (fun projectee -> (match (projectee) with
| Record (_59_55) -> begin
_59_55
end))

# 61 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Project____0 : term'  ->  (term * FStar_Ident.lid) = (fun projectee -> (match (projectee) with
| Project (_59_58) -> begin
_59_58
end))

# 62 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Product____0 : term'  ->  (binder Prims.list * term) = (fun projectee -> (match (projectee) with
| Product (_59_61) -> begin
_59_61
end))

# 63 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Sum____0 : term'  ->  (binder Prims.list * term) = (fun projectee -> (match (projectee) with
| Sum (_59_64) -> begin
_59_64
end))

# 64 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___QForall____0 : term'  ->  (binder Prims.list * term Prims.list Prims.list * term) = (fun projectee -> (match (projectee) with
| QForall (_59_67) -> begin
_59_67
end))

# 65 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___QExists____0 : term'  ->  (binder Prims.list * term Prims.list Prims.list * term) = (fun projectee -> (match (projectee) with
| QExists (_59_70) -> begin
_59_70
end))

# 66 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Refine____0 : term'  ->  (binder * term) = (fun projectee -> (match (projectee) with
| Refine (_59_73) -> begin
_59_73
end))

# 67 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___NamedTyp____0 : term'  ->  (FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| NamedTyp (_59_76) -> begin
_59_76
end))

# 68 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Paren____0 : term'  ->  term = (fun projectee -> (match (projectee) with
| Paren (_59_79) -> begin
_59_79
end))

# 69 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Requires____0 : term'  ->  (term * Prims.string Prims.option) = (fun projectee -> (match (projectee) with
| Requires (_59_82) -> begin
_59_82
end))

# 70 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Ensures____0 : term'  ->  (term * Prims.string Prims.option) = (fun projectee -> (match (projectee) with
| Ensures (_59_85) -> begin
_59_85
end))

# 71 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Labeled____0 : term'  ->  (term * Prims.string * Prims.bool) = (fun projectee -> (match (projectee) with
| Labeled (_59_88) -> begin
_59_88
end))

# 76 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Variable____0 : binder'  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| Variable (_59_92) -> begin
_59_92
end))

# 77 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___TVariable____0 : binder'  ->  FStar_Ident.ident = (fun projectee -> (match (projectee) with
| TVariable (_59_95) -> begin
_59_95
end))

# 78 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Annotated____0 : binder'  ->  (FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| Annotated (_59_98) -> begin
_59_98
end))

# 79 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___TAnnotated____0 : binder'  ->  (FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| TAnnotated (_59_101) -> begin
_59_101
end))

# 80 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___NoName____0 : binder'  ->  term = (fun projectee -> (match (projectee) with
| NoName (_59_104) -> begin
_59_104
end))

# 85 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___PatConst____0 : pattern'  ->  FStar_Const.sconst = (fun projectee -> (match (projectee) with
| PatConst (_59_108) -> begin
_59_108
end))

# 86 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___PatApp____0 : pattern'  ->  (pattern * pattern Prims.list) = (fun projectee -> (match (projectee) with
| PatApp (_59_111) -> begin
_59_111
end))

# 87 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___PatVar____0 : pattern'  ->  (FStar_Ident.ident * Prims.bool) = (fun projectee -> (match (projectee) with
| PatVar (_59_114) -> begin
_59_114
end))

# 88 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___PatName____0 : pattern'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| PatName (_59_117) -> begin
_59_117
end))

# 89 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___PatTvar____0 : pattern'  ->  (FStar_Ident.ident * Prims.bool) = (fun projectee -> (match (projectee) with
| PatTvar (_59_120) -> begin
_59_120
end))

# 90 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___PatList____0 : pattern'  ->  pattern Prims.list = (fun projectee -> (match (projectee) with
| PatList (_59_123) -> begin
_59_123
end))

# 91 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___PatTuple____0 : pattern'  ->  (pattern Prims.list * Prims.bool) = (fun projectee -> (match (projectee) with
| PatTuple (_59_126) -> begin
_59_126
end))

# 92 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___PatRecord____0 : pattern'  ->  (FStar_Ident.lid * pattern) Prims.list = (fun projectee -> (match (projectee) with
| PatRecord (_59_129) -> begin
_59_129
end))

# 93 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___PatAscribed____0 : pattern'  ->  (pattern * term) = (fun projectee -> (match (projectee) with
| PatAscribed (_59_132) -> begin
_59_132
end))

# 94 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___PatOr____0 : pattern'  ->  pattern Prims.list = (fun projectee -> (match (projectee) with
| PatOr (_59_135) -> begin
_59_135
end))

# 97 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type knd =
term

# 99 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type typ =
term

# 100 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type expr =
term

# 101 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type tycon =
| TyconAbstract of (FStar_Ident.ident * binder Prims.list * knd Prims.option)
| TyconAbbrev of (FStar_Ident.ident * binder Prims.list * knd Prims.option * term)
| TyconRecord of (FStar_Ident.ident * binder Prims.list * knd Prims.option * (FStar_Ident.ident * term) Prims.list)
| TyconVariant of (FStar_Ident.ident * binder Prims.list * knd Prims.option * (FStar_Ident.ident * term Prims.option * Prims.bool) Prims.list)

# 104 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_TyconAbstract = (fun _discr_ -> (match (_discr_) with
| TyconAbstract (_) -> begin
true
end
| _ -> begin
false
end))

# 105 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_TyconAbbrev = (fun _discr_ -> (match (_discr_) with
| TyconAbbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 106 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_TyconRecord = (fun _discr_ -> (match (_discr_) with
| TyconRecord (_) -> begin
true
end
| _ -> begin
false
end))

# 107 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_TyconVariant = (fun _discr_ -> (match (_discr_) with
| TyconVariant (_) -> begin
true
end
| _ -> begin
false
end))

# 104 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___TyconAbstract____0 : tycon  ->  (FStar_Ident.ident * binder Prims.list * knd Prims.option) = (fun projectee -> (match (projectee) with
| TyconAbstract (_59_139) -> begin
_59_139
end))

# 105 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___TyconAbbrev____0 : tycon  ->  (FStar_Ident.ident * binder Prims.list * knd Prims.option * term) = (fun projectee -> (match (projectee) with
| TyconAbbrev (_59_142) -> begin
_59_142
end))

# 106 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___TyconRecord____0 : tycon  ->  (FStar_Ident.ident * binder Prims.list * knd Prims.option * (FStar_Ident.ident * term) Prims.list) = (fun projectee -> (match (projectee) with
| TyconRecord (_59_145) -> begin
_59_145
end))

# 107 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___TyconVariant____0 : tycon  ->  (FStar_Ident.ident * binder Prims.list * knd Prims.option * (FStar_Ident.ident * term Prims.option * Prims.bool) Prims.list) = (fun projectee -> (match (projectee) with
| TyconVariant (_59_148) -> begin
_59_148
end))

# 107 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type qualifier =
| Private
| Abstract
| Assumption
| DefaultEffect
| TotalEffect
| Effect
| New
| Inline
| Unfoldable
| Irreducible
| Opaque
| Logic

# 110 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Private = (fun _discr_ -> (match (_discr_) with
| Private (_) -> begin
true
end
| _ -> begin
false
end))

# 111 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Abstract = (fun _discr_ -> (match (_discr_) with
| Abstract (_) -> begin
true
end
| _ -> begin
false
end))

# 112 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Assumption = (fun _discr_ -> (match (_discr_) with
| Assumption (_) -> begin
true
end
| _ -> begin
false
end))

# 113 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_DefaultEffect = (fun _discr_ -> (match (_discr_) with
| DefaultEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 114 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_TotalEffect = (fun _discr_ -> (match (_discr_) with
| TotalEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 115 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Effect = (fun _discr_ -> (match (_discr_) with
| Effect (_) -> begin
true
end
| _ -> begin
false
end))

# 116 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_New = (fun _discr_ -> (match (_discr_) with
| New (_) -> begin
true
end
| _ -> begin
false
end))

# 117 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Inline = (fun _discr_ -> (match (_discr_) with
| Inline (_) -> begin
true
end
| _ -> begin
false
end))

# 118 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Unfoldable = (fun _discr_ -> (match (_discr_) with
| Unfoldable (_) -> begin
true
end
| _ -> begin
false
end))

# 119 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Irreducible = (fun _discr_ -> (match (_discr_) with
| Irreducible (_) -> begin
true
end
| _ -> begin
false
end))

# 121 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Opaque = (fun _discr_ -> (match (_discr_) with
| Opaque (_) -> begin
true
end
| _ -> begin
false
end))

# 122 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Logic = (fun _discr_ -> (match (_discr_) with
| Logic (_) -> begin
true
end
| _ -> begin
false
end))

# 122 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type qualifiers =
qualifier Prims.list

# 126 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type lift =
{msource : FStar_Ident.lid; mdest : FStar_Ident.lid; lift_op : term}

# 128 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Mklift : lift  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklift"))))

# 132 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type pragma =
| SetOptions of Prims.string
| ResetOptions

# 135 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_SetOptions = (fun _discr_ -> (match (_discr_) with
| SetOptions (_) -> begin
true
end
| _ -> begin
false
end))

# 136 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_ResetOptions = (fun _discr_ -> (match (_discr_) with
| ResetOptions (_) -> begin
true
end
| _ -> begin
false
end))

# 135 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___SetOptions____0 : pragma  ->  Prims.string = (fun projectee -> (match (projectee) with
| SetOptions (_59_155) -> begin
_59_155
end))

# 136 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type decl' =
| TopLevelModule of FStar_Ident.lid
| Open of FStar_Ident.lid
| ModuleAbbrev of (FStar_Ident.ident * FStar_Ident.lid)
| KindAbbrev of (FStar_Ident.ident * binder Prims.list * knd)
| ToplevelLet of (qualifiers * Prims.bool * (pattern * term) Prims.list)
| Main of term
| Assume of (qualifiers * FStar_Ident.ident * term)
| Tycon of (qualifiers * tycon Prims.list)
| Val of (qualifiers * FStar_Ident.ident * term)
| Exception of (FStar_Ident.ident * term Prims.option)
| NewEffect of (qualifiers * effect_decl)
| SubEffect of lift
| Pragma of pragma 
 and decl =
{d : decl'; drange : FStar_Range.range} 
 and effect_decl =
| DefineEffect of (FStar_Ident.ident * binder Prims.list * term * decl Prims.list)
| RedefineEffect of (FStar_Ident.ident * binder Prims.list * term)

# 139 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_TopLevelModule = (fun _discr_ -> (match (_discr_) with
| TopLevelModule (_) -> begin
true
end
| _ -> begin
false
end))

# 140 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Open = (fun _discr_ -> (match (_discr_) with
| Open (_) -> begin
true
end
| _ -> begin
false
end))

# 141 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_ModuleAbbrev = (fun _discr_ -> (match (_discr_) with
| ModuleAbbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 142 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_KindAbbrev = (fun _discr_ -> (match (_discr_) with
| KindAbbrev (_) -> begin
true
end
| _ -> begin
false
end))

# 143 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_ToplevelLet = (fun _discr_ -> (match (_discr_) with
| ToplevelLet (_) -> begin
true
end
| _ -> begin
false
end))

# 144 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Main = (fun _discr_ -> (match (_discr_) with
| Main (_) -> begin
true
end
| _ -> begin
false
end))

# 145 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Assume = (fun _discr_ -> (match (_discr_) with
| Assume (_) -> begin
true
end
| _ -> begin
false
end))

# 146 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Tycon = (fun _discr_ -> (match (_discr_) with
| Tycon (_) -> begin
true
end
| _ -> begin
false
end))

# 147 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Val = (fun _discr_ -> (match (_discr_) with
| Val (_) -> begin
true
end
| _ -> begin
false
end))

# 148 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Exception = (fun _discr_ -> (match (_discr_) with
| Exception (_) -> begin
true
end
| _ -> begin
false
end))

# 149 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_NewEffect = (fun _discr_ -> (match (_discr_) with
| NewEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 150 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_SubEffect = (fun _discr_ -> (match (_discr_) with
| SubEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 151 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Pragma = (fun _discr_ -> (match (_discr_) with
| Pragma (_) -> begin
true
end
| _ -> begin
false
end))

# 152 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Mkdecl : decl  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdecl"))))

# 154 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_DefineEffect = (fun _discr_ -> (match (_discr_) with
| DefineEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 155 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_RedefineEffect = (fun _discr_ -> (match (_discr_) with
| RedefineEffect (_) -> begin
true
end
| _ -> begin
false
end))

# 139 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___TopLevelModule____0 : decl'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| TopLevelModule (_59_160) -> begin
_59_160
end))

# 140 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Open____0 : decl'  ->  FStar_Ident.lid = (fun projectee -> (match (projectee) with
| Open (_59_163) -> begin
_59_163
end))

# 141 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___ModuleAbbrev____0 : decl'  ->  (FStar_Ident.ident * FStar_Ident.lid) = (fun projectee -> (match (projectee) with
| ModuleAbbrev (_59_166) -> begin
_59_166
end))

# 142 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___KindAbbrev____0 : decl'  ->  (FStar_Ident.ident * binder Prims.list * knd) = (fun projectee -> (match (projectee) with
| KindAbbrev (_59_169) -> begin
_59_169
end))

# 143 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___ToplevelLet____0 : decl'  ->  (qualifiers * Prims.bool * (pattern * term) Prims.list) = (fun projectee -> (match (projectee) with
| ToplevelLet (_59_172) -> begin
_59_172
end))

# 144 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Main____0 : decl'  ->  term = (fun projectee -> (match (projectee) with
| Main (_59_175) -> begin
_59_175
end))

# 145 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Assume____0 : decl'  ->  (qualifiers * FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| Assume (_59_178) -> begin
_59_178
end))

# 146 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Tycon____0 : decl'  ->  (qualifiers * tycon Prims.list) = (fun projectee -> (match (projectee) with
| Tycon (_59_181) -> begin
_59_181
end))

# 147 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Val____0 : decl'  ->  (qualifiers * FStar_Ident.ident * term) = (fun projectee -> (match (projectee) with
| Val (_59_184) -> begin
_59_184
end))

# 148 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Exception____0 : decl'  ->  (FStar_Ident.ident * term Prims.option) = (fun projectee -> (match (projectee) with
| Exception (_59_187) -> begin
_59_187
end))

# 149 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___NewEffect____0 : decl'  ->  (qualifiers * effect_decl) = (fun projectee -> (match (projectee) with
| NewEffect (_59_190) -> begin
_59_190
end))

# 150 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___SubEffect____0 : decl'  ->  lift = (fun projectee -> (match (projectee) with
| SubEffect (_59_193) -> begin
_59_193
end))

# 151 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Pragma____0 : decl'  ->  pragma = (fun projectee -> (match (projectee) with
| Pragma (_59_196) -> begin
_59_196
end))

# 154 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___DefineEffect____0 : effect_decl  ->  (FStar_Ident.ident * binder Prims.list * term * decl Prims.list) = (fun projectee -> (match (projectee) with
| DefineEffect (_59_200) -> begin
_59_200
end))

# 155 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___RedefineEffect____0 : effect_decl  ->  (FStar_Ident.ident * binder Prims.list * term) = (fun projectee -> (match (projectee) with
| RedefineEffect (_59_203) -> begin
_59_203
end))

# 155 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type modul =
| Module of (FStar_Ident.lid * decl Prims.list)
| Interface of (FStar_Ident.lid * decl Prims.list * Prims.bool)

# 158 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Module = (fun _discr_ -> (match (_discr_) with
| Module (_) -> begin
true
end
| _ -> begin
false
end))

# 159 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let is_Interface = (fun _discr_ -> (match (_discr_) with
| Interface (_) -> begin
true
end
| _ -> begin
false
end))

# 158 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Module____0 : modul  ->  (FStar_Ident.lid * decl Prims.list) = (fun projectee -> (match (projectee) with
| Module (_59_206) -> begin
_59_206
end))

# 159 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let ___Interface____0 : modul  ->  (FStar_Ident.lid * decl Prims.list * Prims.bool) = (fun projectee -> (match (projectee) with
| Interface (_59_209) -> begin
_59_209
end))

# 159 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type file =
modul Prims.list

# 160 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

type inputFragment =
(file, decl Prims.list) FStar_Util.either

# 161 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let mk_decl : decl'  ->  FStar_Range.range  ->  decl = (fun d r -> {d = d; drange = r})

# 164 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let mk_binder : binder'  ->  FStar_Range.range  ->  level  ->  aqual  ->  binder = (fun b r l i -> {b = b; brange = r; blevel = l; aqual = i})

# 165 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let mk_term : term'  ->  FStar_Range.range  ->  level  ->  term = (fun t r l -> {tm = t; range = r; level = l})

# 166 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let mk_pattern : pattern'  ->  FStar_Range.range  ->  pattern = (fun p r -> {pat = p; prange = r})

# 167 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let un_curry_abs : pattern Prims.list  ->  term  ->  term' = (fun ps body -> (match (body.tm) with
| Abs (p', body') -> begin
Abs (((FStar_List.append ps p'), body'))
end
| _59_228 -> begin
Abs ((ps, body))
end))

# 170 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let mk_function : branch Prims.list  ->  FStar_Range.range  ->  FStar_Range.range  ->  term = (fun branches r1 r2 -> (let x = (FStar_Absyn_Util.genident (Some (r1)))
in (let _161_994 = (let _161_993 = (let _161_992 = (let _161_991 = (let _161_990 = (let _161_989 = (let _161_988 = (let _161_987 = (FStar_Ident.lid_of_ids ((x)::[]))
in Var (_161_987))
in (mk_term _161_988 r1 Expr))
in (_161_989, branches))
in Match (_161_990))
in (mk_term _161_991 r2 Expr))
in (((mk_pattern (PatVar ((x, false))) r1))::[], _161_992))
in Abs (_161_993))
in (mk_term _161_994 r2 Expr))))

# 175 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let un_function : pattern  ->  term  ->  (pattern * term) Prims.option = (fun p tm -> (match ((p.pat, tm.tm)) with
| (PatVar (_59_236), Abs (pats, body)) -> begin
Some (((mk_pattern (PatApp ((p, pats))) p.prange), body))
end
| _59_244 -> begin
None
end))

# 178 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let lid_with_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun lid r -> (let _161_1003 = (FStar_Ident.path_of_lid lid)
in (FStar_Ident.lid_of_path _161_1003 r)))

# 180 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let to_string_l = (fun sep f l -> (let _161_1010 = (FStar_List.map f l)
in (FStar_String.concat sep _161_1010)))

# 183 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let imp_to_string : imp  ->  Prims.string = (fun _59_1 -> (match (_59_1) with
| Hash -> begin
"#"
end
| _59_253 -> begin
""
end))

# 186 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let rec term_to_string : term  ->  Prims.string = (fun x -> (match (x.tm) with
| Wild -> begin
"_"
end
| Requires (t, _59_258) -> begin
(let _161_1017 = (term_to_string t)
in (FStar_Util.format1 "(requires %s)" _161_1017))
end
| Ensures (t, _59_263) -> begin
(let _161_1018 = (term_to_string t)
in (FStar_Util.format1 "(ensures %s)" _161_1018))
end
| Labeled (t, l, _59_269) -> begin
(let _161_1019 = (term_to_string t)
in (FStar_Util.format2 "(labeled %s %s)" l _161_1019))
end
| Const (c) -> begin
(FStar_Absyn_Print.const_to_string c)
end
| Op (s, xs) -> begin
(let _161_1022 = (let _161_1021 = (FStar_List.map (fun x -> (FStar_All.pipe_right x term_to_string)) xs)
in (FStar_String.concat ", " _161_1021))
in (FStar_Util.format2 "%s(%s)" s _161_1022))
end
| Tvar (id) -> begin
id.FStar_Ident.idText
end
| (Var (l)) | (Name (l)) -> begin
l.FStar_Ident.str
end
| Construct (l, args) -> begin
(let _161_1025 = (to_string_l " " (fun _59_290 -> (match (_59_290) with
| (a, imp) -> begin
(let _161_1024 = (term_to_string a)
in (FStar_Util.format2 "%s%s" (imp_to_string imp) _161_1024))
end)) args)
in (FStar_Util.format2 "(%s %s)" l.FStar_Ident.str _161_1025))
end
| Abs (pats, t) when (x.level = Expr) -> begin
(let _161_1027 = (to_string_l " " pat_to_string pats)
in (let _161_1026 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s -> %s)" _161_1027 _161_1026)))
end
| Abs (pats, t) when (x.level = Type) -> begin
(let _161_1029 = (to_string_l " " pat_to_string pats)
in (let _161_1028 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(fun %s => %s)" _161_1029 _161_1028)))
end
| App (t1, t2, imp) -> begin
(let _161_1031 = (FStar_All.pipe_right t1 term_to_string)
in (let _161_1030 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format3 "%s %s%s" _161_1031 (imp_to_string imp) _161_1030)))
end
| Let (false, (pat, tm)::[], body) -> begin
(let _161_1034 = (FStar_All.pipe_right pat pat_to_string)
in (let _161_1033 = (FStar_All.pipe_right tm term_to_string)
in (let _161_1032 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format3 "let %s = %s in %s" _161_1034 _161_1033 _161_1032))))
end
| Let (_59_313, lbs, body) -> begin
(let _161_1039 = (to_string_l " and " (fun _59_320 -> (match (_59_320) with
| (p, b) -> begin
(let _161_1037 = (FStar_All.pipe_right p pat_to_string)
in (let _161_1036 = (FStar_All.pipe_right b term_to_string)
in (FStar_Util.format2 "%s=%s" _161_1037 _161_1036)))
end)) lbs)
in (let _161_1038 = (FStar_All.pipe_right body term_to_string)
in (FStar_Util.format2 "let rec %s in %s" _161_1039 _161_1038)))
end
| Seq (t1, t2) -> begin
(let _161_1041 = (FStar_All.pipe_right t1 term_to_string)
in (let _161_1040 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "%s; %s" _161_1041 _161_1040)))
end
| If (t1, t2, t3) -> begin
(let _161_1044 = (FStar_All.pipe_right t1 term_to_string)
in (let _161_1043 = (FStar_All.pipe_right t2 term_to_string)
in (let _161_1042 = (FStar_All.pipe_right t3 term_to_string)
in (FStar_Util.format3 "if %s then %s else %s" _161_1044 _161_1043 _161_1042))))
end
| Match (t, branches) -> begin
(let _161_1051 = (FStar_All.pipe_right t term_to_string)
in (let _161_1050 = (to_string_l " | " (fun _59_337 -> (match (_59_337) with
| (p, w, e) -> begin
(let _161_1049 = (FStar_All.pipe_right p pat_to_string)
in (let _161_1048 = (match (w) with
| None -> begin
""
end
| Some (e) -> begin
(let _161_1046 = (term_to_string e)
in (FStar_Util.format1 "when %s" _161_1046))
end)
in (let _161_1047 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" _161_1049 _161_1048 _161_1047))))
end)) branches)
in (FStar_Util.format2 "match %s with %s" _161_1051 _161_1050)))
end
| Ascribed (t1, t2) -> begin
(let _161_1053 = (FStar_All.pipe_right t1 term_to_string)
in (let _161_1052 = (FStar_All.pipe_right t2 term_to_string)
in (FStar_Util.format2 "(%s : %s)" _161_1053 _161_1052)))
end
| Record (Some (e), fields) -> begin
(let _161_1057 = (FStar_All.pipe_right e term_to_string)
in (let _161_1056 = (to_string_l " " (fun _59_352 -> (match (_59_352) with
| (l, e) -> begin
(let _161_1055 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _161_1055))
end)) fields)
in (FStar_Util.format2 "{%s with %s}" _161_1057 _161_1056)))
end
| Record (None, fields) -> begin
(let _161_1060 = (to_string_l " " (fun _59_359 -> (match (_59_359) with
| (l, e) -> begin
(let _161_1059 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s=%s" l.FStar_Ident.str _161_1059))
end)) fields)
in (FStar_Util.format1 "{%s}" _161_1060))
end
| Project (e, l) -> begin
(let _161_1061 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format2 "%s.%s" _161_1061 l.FStar_Ident.str))
end
| Product ([], t) -> begin
(term_to_string t)
end
| Product (b::hd::tl, t) -> begin
(term_to_string (mk_term (Product (((b)::[], (mk_term (Product (((hd)::tl, t))) x.range x.level)))) x.range x.level))
end
| Product (b::[], t) when (x.level = Type) -> begin
(let _161_1063 = (FStar_All.pipe_right b binder_to_string)
in (let _161_1062 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s -> %s" _161_1063 _161_1062)))
end
| Product (b::[], t) when (x.level = Kind) -> begin
(let _161_1065 = (FStar_All.pipe_right b binder_to_string)
in (let _161_1064 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s => %s" _161_1065 _161_1064)))
end
| Sum (binders, t) -> begin
(let _161_1068 = (let _161_1066 = (FStar_All.pipe_right binders (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _161_1066 (FStar_String.concat " * ")))
in (let _161_1067 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s * %s" _161_1068 _161_1067)))
end
| QForall (bs, pats, t) -> begin
(let _161_1071 = (to_string_l " " binder_to_string bs)
in (let _161_1070 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _161_1069 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "forall %s.{:pattern %s} %s" _161_1071 _161_1070 _161_1069))))
end
| QExists (bs, pats, t) -> begin
(let _161_1074 = (to_string_l " " binder_to_string bs)
in (let _161_1073 = (to_string_l " \\/ " (to_string_l "; " term_to_string) pats)
in (let _161_1072 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format3 "exists %s.{:pattern %s} %s" _161_1074 _161_1073 _161_1072))))
end
| Refine (b, t) -> begin
(let _161_1076 = (FStar_All.pipe_right b binder_to_string)
in (let _161_1075 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:{%s}" _161_1076 _161_1075)))
end
| NamedTyp (x, t) -> begin
(let _161_1077 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" x.FStar_Ident.idText _161_1077))
end
| Paren (t) -> begin
(let _161_1078 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format1 "(%s)" _161_1078))
end
| Product (bs, t) -> begin
(let _161_1081 = (let _161_1079 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right _161_1079 (FStar_String.concat ",")))
in (let _161_1080 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "Unidentified product: [%s] %s" _161_1081 _161_1080)))
end
| t -> begin
(FStar_All.failwith "Missing case in term_to_string")
end))
and binder_to_string : binder  ->  Prims.string = (fun x -> (let s = (match (x.b) with
| Variable (i) -> begin
i.FStar_Ident.idText
end
| TVariable (i) -> begin
(FStar_Util.format1 "%s:_" i.FStar_Ident.idText)
end
| (TAnnotated (i, t)) | (Annotated (i, t)) -> begin
(let _161_1083 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "%s:%s" i.FStar_Ident.idText _161_1083))
end
| NoName (t) -> begin
(FStar_All.pipe_right t term_to_string)
end)
in (match (x.aqual) with
| Some (Implicit) -> begin
(FStar_Util.format1 "#%s" s)
end
| Some (Equality) -> begin
(FStar_Util.format1 "=%s" s)
end
| _59_434 -> begin
s
end)))
and pat_to_string : pattern  ->  Prims.string = (fun x -> (match (x.pat) with
| PatWild -> begin
"_"
end
| PatConst (c) -> begin
(FStar_Absyn_Print.const_to_string c)
end
| PatApp (p, ps) -> begin
(let _161_1086 = (FStar_All.pipe_right p pat_to_string)
in (let _161_1085 = (to_string_l " " pat_to_string ps)
in (FStar_Util.format2 "(%s %s)" _161_1086 _161_1085)))
end
| (PatTvar (i, true)) | (PatVar (i, true)) -> begin
(FStar_Util.format1 "#%s" i.FStar_Ident.idText)
end
| (PatTvar (i, false)) | (PatVar (i, false)) -> begin
i.FStar_Ident.idText
end
| PatName (l) -> begin
l.FStar_Ident.str
end
| PatList (l) -> begin
(let _161_1087 = (to_string_l "; " pat_to_string l)
in (FStar_Util.format1 "[%s]" _161_1087))
end
| PatTuple (l, false) -> begin
(let _161_1088 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(%s)" _161_1088))
end
| PatTuple (l, true) -> begin
(let _161_1089 = (to_string_l ", " pat_to_string l)
in (FStar_Util.format1 "(|%s|)" _161_1089))
end
| PatRecord (l) -> begin
(let _161_1092 = (to_string_l "; " (fun _59_473 -> (match (_59_473) with
| (f, e) -> begin
(let _161_1091 = (FStar_All.pipe_right e pat_to_string)
in (FStar_Util.format2 "%s=%s" f.FStar_Ident.str _161_1091))
end)) l)
in (FStar_Util.format1 "{%s}" _161_1092))
end
| PatOr (l) -> begin
(to_string_l "|\n " pat_to_string l)
end
| PatAscribed (p, t) -> begin
(let _161_1094 = (FStar_All.pipe_right p pat_to_string)
in (let _161_1093 = (FStar_All.pipe_right t term_to_string)
in (FStar_Util.format2 "(%s:%s)" _161_1094 _161_1093)))
end))

# 283 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let error = (fun msg tm r -> (let tm = (FStar_All.pipe_right tm term_to_string)
in (let tm = if ((FStar_String.length tm) >= 80) then begin
(let _161_1098 = (FStar_Util.substring tm 0 77)
in (Prims.strcat _161_1098 "..."))
end else begin
tm
end
in (Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat msg "\n") tm), r)))))))

# 288 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let consPat : FStar_Range.range  ->  pattern  ->  pattern  ->  pattern' = (fun r hd tl -> PatApp (((mk_pattern (PatName (FStar_Absyn_Const.cons_lid)) r), (hd)::(tl)::[])))

# 290 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let consTerm : FStar_Range.range  ->  term  ->  term  ->  term = (fun r hd tl -> (mk_term (Construct ((FStar_Absyn_Const.cons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))

# 291 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let lexConsTerm : FStar_Range.range  ->  term  ->  term  ->  term = (fun r hd tl -> (mk_term (Construct ((FStar_Absyn_Const.lexcons_lid, ((hd, Nothing))::((tl, Nothing))::[]))) r Expr))

# 292 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let mkConsList : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (let nil = (mk_term (Construct ((FStar_Absyn_Const.nil_lid, []))) r Expr)
in (FStar_List.fold_right (fun e tl -> (consTerm r e tl)) elts nil)))

# 296 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let mkLexList : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (let nil = (mk_term (Construct ((FStar_Absyn_Const.lextop_lid, []))) r Expr)
in (FStar_List.fold_right (fun e tl -> (lexConsTerm r e tl)) elts nil)))

# 300 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let mkApp : term  ->  (term * imp) Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _59_509 -> begin
(match (t.tm) with
| Name (s) -> begin
(mk_term (Construct ((s, args))) r Un)
end
| _59_513 -> begin
(FStar_List.fold_left (fun t _59_517 -> (match (_59_517) with
| (a, imp) -> begin
(mk_term (App ((t, a, imp))) r Un)
end)) t args)
end)
end))

# 306 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let mkRefSet : FStar_Range.range  ->  term Prims.list  ->  term = (fun r elts -> (let empty = (let _161_1142 = (let _161_1141 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_empty r)
in Var (_161_1141))
in (mk_term _161_1142 r Expr))
in (let ref_constr = (let _161_1144 = (let _161_1143 = (FStar_Ident.set_lid_range FStar_Absyn_Const.heap_ref r)
in Var (_161_1143))
in (mk_term _161_1144 r Expr))
in (let singleton = (let _161_1146 = (let _161_1145 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_singleton r)
in Var (_161_1145))
in (mk_term _161_1146 r Expr))
in (let union = (let _161_1148 = (let _161_1147 = (FStar_Ident.set_lid_range FStar_Absyn_Const.set_union r)
in Var (_161_1147))
in (mk_term _161_1148 r Expr))
in (FStar_List.fold_right (fun e tl -> (let e = (mkApp ref_constr (((e, Nothing))::[]) r)
in (let single_e = (mkApp singleton (((e, Nothing))::[]) r)
in (mkApp union (((single_e, Nothing))::((tl, Nothing))::[]) r)))) elts empty))))))

# 316 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let mkExplicitApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (match (args) with
| [] -> begin
t
end
| _59_533 -> begin
(match (t.tm) with
| Name (s) -> begin
(let _161_1160 = (let _161_1159 = (let _161_1158 = (FStar_List.map (fun a -> (a, Nothing)) args)
in (s, _161_1158))
in Construct (_161_1159))
in (mk_term _161_1160 r Un))
end
| _59_538 -> begin
(FStar_List.fold_left (fun t a -> (mk_term (App ((t, a, Nothing))) r Un)) t args)
end)
end))

# 322 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let mkAdmitMagic : FStar_Range.range  ->  term = (fun r -> (let unit_const = (mk_term (Const (FStar_Const.Const_unit)) r Expr)
in (let admit = (let admit_name = (let _161_1166 = (let _161_1165 = (FStar_Ident.set_lid_range FStar_Absyn_Const.admit_lid r)
in Var (_161_1165))
in (mk_term _161_1166 r Expr))
in (mkExplicitApp admit_name ((unit_const)::[]) r))
in (let magic = (let magic_name = (let _161_1168 = (let _161_1167 = (FStar_Ident.set_lid_range FStar_Absyn_Const.magic_lid r)
in Var (_161_1167))
in (mk_term _161_1168 r Expr))
in (mkExplicitApp magic_name ((unit_const)::[]) r))
in (let admit_magic = (mk_term (Seq ((admit, magic))) r Expr)
in admit_magic)))))

# 333 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let mkWildAdmitMagic = (fun r -> (let _161_1170 = (mkAdmitMagic r)
in ((mk_pattern PatWild r), None, _161_1170)))

# 335 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let focusBranches = (fun branches r -> (let should_filter = (FStar_Util.for_some Prims.fst branches)
in if should_filter then begin
(let _59_552 = (FStar_Tc_Errors.warn r "Focusing on only some cases")
in (let focussed = (let _161_1173 = (FStar_List.filter Prims.fst branches)
in (FStar_All.pipe_right _161_1173 (FStar_List.map Prims.snd)))
in (let _161_1175 = (let _161_1174 = (mkWildAdmitMagic r)
in (_161_1174)::[])
in (FStar_List.append focussed _161_1175))))
end else begin
(FStar_All.pipe_right branches (FStar_List.map Prims.snd))
end))

# 343 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let focusLetBindings = (fun lbs r -> (let should_filter = (FStar_Util.for_some Prims.fst lbs)
in if should_filter then begin
(let _59_558 = (FStar_Tc_Errors.warn r "Focusing on only some cases in this (mutually) recursive definition")
in (FStar_List.map (fun _59_562 -> (match (_59_562) with
| (f, lb) -> begin
if f then begin
lb
end else begin
(let _161_1179 = (mkAdmitMagic r)
in ((Prims.fst lb), _161_1179))
end
end)) lbs))
end else begin
(FStar_All.pipe_right lbs (FStar_List.map Prims.snd))
end))

# 352 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let mkFsTypApp : term  ->  term Prims.list  ->  FStar_Range.range  ->  term = (fun t args r -> (let _161_1187 = (FStar_List.map (fun a -> (a, FsTypApp)) args)
in (mkApp t _161_1187 r)))

# 355 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let mkTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (let cons = (FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) r)
in (let _161_1193 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _161_1193 r))))

# 359 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let mkDTuple : term Prims.list  ->  FStar_Range.range  ->  term = (fun args r -> (let cons = (FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) r)
in (let _161_1199 = (FStar_List.map (fun x -> (x, Nothing)) args)
in (mkApp (mk_term (Name (cons)) r Expr) _161_1199 r))))

# 363 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let mkRefinedBinder : FStar_Ident.ident  ->  term  ->  term Prims.option  ->  FStar_Range.range  ->  aqual  ->  binder = (fun id t refopt m implicit -> (let b = (mk_binder (Annotated ((id, t))) m Type implicit)
in (match (refopt) with
| None -> begin
b
end
| Some (t) -> begin
(mk_binder (Annotated ((id, (mk_term (Refine ((b, t))) m Type)))) m Type implicit)
end)))

# 369 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\parser\\ast.fs"

let rec extract_named_refinement : term  ->  (FStar_Ident.ident * term * term Prims.option) Prims.option = (fun t1 -> (match (t1.tm) with
| NamedTyp (x, t) -> begin
Some ((x, t, None))
end
| Refine ({b = Annotated (x, t); brange = _59_594; blevel = _59_592; aqual = _59_590}, t') -> begin
Some ((x, t, Some (t')))
end
| Paren (t) -> begin
(extract_named_refinement t)
end
| _59_606 -> begin
None
end))




