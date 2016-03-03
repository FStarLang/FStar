
open Prims
# 26 "FStar.TypeChecker.Common.fst"
type rel =
| EQ
| SUB
| SUBINV

# 27 "FStar.TypeChecker.Common.fst"
let is_EQ = (fun _discr_ -> (match (_discr_) with
| EQ (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.TypeChecker.Common.fst"
let is_SUB = (fun _discr_ -> (match (_discr_) with
| SUB (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "FStar.TypeChecker.Common.fst"
let is_SUBINV = (fun _discr_ -> (match (_discr_) with
| SUBINV (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "FStar.TypeChecker.Common.fst"
type ('a, 'b) problem =
{pid : Prims.int; lhs : 'a; relation : rel; rhs : 'a; element : 'b Prims.option; logical_guard : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term); scope : FStar_Syntax_Syntax.binders; reason : Prims.string Prims.list; loc : FStar_Range.range; rank : Prims.int Prims.option}

# 31 "FStar.TypeChecker.Common.fst"
let is_Mkproblem = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkproblem"))))

# 44 "FStar.TypeChecker.Common.fst"
type prob =
| TProb of (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) problem
| CProb of (FStar_Syntax_Syntax.comp, Prims.unit) problem

# 45 "FStar.TypeChecker.Common.fst"
let is_TProb = (fun _discr_ -> (match (_discr_) with
| TProb (_) -> begin
true
end
| _ -> begin
false
end))

# 46 "FStar.TypeChecker.Common.fst"
let is_CProb = (fun _discr_ -> (match (_discr_) with
| CProb (_) -> begin
true
end
| _ -> begin
false
end))

# 45 "FStar.TypeChecker.Common.fst"
let ___TProb____0 : prob  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) problem = (fun projectee -> (match (projectee) with
| TProb (_64_16) -> begin
_64_16
end))

# 46 "FStar.TypeChecker.Common.fst"
let ___CProb____0 : prob  ->  (FStar_Syntax_Syntax.comp, Prims.unit) problem = (fun projectee -> (match (projectee) with
| CProb (_64_19) -> begin
_64_19
end))

# 48 "FStar.TypeChecker.Common.fst"
type probs =
prob Prims.list

# 50 "FStar.TypeChecker.Common.fst"
type guard_formula =
| Trivial
| NonTrivial of FStar_Syntax_Syntax.formula

# 51 "FStar.TypeChecker.Common.fst"
let is_Trivial = (fun _discr_ -> (match (_discr_) with
| Trivial (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.TypeChecker.Common.fst"
let is_NonTrivial = (fun _discr_ -> (match (_discr_) with
| NonTrivial (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.TypeChecker.Common.fst"
let ___NonTrivial____0 : guard_formula  ->  FStar_Syntax_Syntax.formula = (fun projectee -> (match (projectee) with
| NonTrivial (_64_22) -> begin
_64_22
end))

# 54 "FStar.TypeChecker.Common.fst"
type deferred =
(Prims.string * prob) Prims.list

# 55 "FStar.TypeChecker.Common.fst"
type univ_ineq =
(FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)

# 60 "FStar.TypeChecker.Common.fst"
let tconst : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun l -> (let _145_84 = (let _145_83 = (let _145_82 = (FStar_Ident.set_lid_range l FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv _145_82 None))
in FStar_Syntax_Syntax.Tm_fvar (_145_83))
in (FStar_Syntax_Syntax.mk _145_84 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) FStar_Range.dummyRange)))

# 61 "FStar.TypeChecker.Common.fst"
let t_unit : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.unit_lid)

# 62 "FStar.TypeChecker.Common.fst"
let t_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.bool_lid)

# 63 "FStar.TypeChecker.Common.fst"
let t_uint8 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.uint8_lid)

# 64 "FStar.TypeChecker.Common.fst"
let t_int : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.int_lid)

# 65 "FStar.TypeChecker.Common.fst"
let t_int32 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.int32_lid)

# 66 "FStar.TypeChecker.Common.fst"
let t_int64 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.int64_lid)

# 67 "FStar.TypeChecker.Common.fst"
let t_string : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.string_lid)

# 68 "FStar.TypeChecker.Common.fst"
let t_float : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.float_lid)

# 69 "FStar.TypeChecker.Common.fst"
let t_char : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.char_lid)




