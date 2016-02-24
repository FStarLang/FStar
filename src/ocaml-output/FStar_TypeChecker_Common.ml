
open Prims
# 25 "FStar.TypeChecker.Common.fst"
type rel =
| EQ
| SUB
| SUBINV

# 26 "FStar.TypeChecker.Common.fst"
let is_EQ = (fun _discr_ -> (match (_discr_) with
| EQ (_) -> begin
true
end
| _ -> begin
false
end))

# 27 "FStar.TypeChecker.Common.fst"
let is_SUB = (fun _discr_ -> (match (_discr_) with
| SUB (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.TypeChecker.Common.fst"
let is_SUBINV = (fun _discr_ -> (match (_discr_) with
| SUBINV (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "FStar.TypeChecker.Common.fst"
type ('a, 'b) problem =
{pid : Prims.int; lhs : 'a; relation : rel; rhs : 'a; element : 'b Prims.option; logical_guard : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term); scope : FStar_Syntax_Syntax.binders; reason : Prims.string Prims.list; loc : FStar_Range.range; rank : Prims.int Prims.option}

# 30 "FStar.TypeChecker.Common.fst"
let is_Mkproblem = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkproblem"))))

# 43 "FStar.TypeChecker.Common.fst"
type prob =
| TProb of (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) problem
| CProb of (FStar_Syntax_Syntax.comp, Prims.unit) problem

# 44 "FStar.TypeChecker.Common.fst"
let is_TProb = (fun _discr_ -> (match (_discr_) with
| TProb (_) -> begin
true
end
| _ -> begin
false
end))

# 45 "FStar.TypeChecker.Common.fst"
let is_CProb = (fun _discr_ -> (match (_discr_) with
| CProb (_) -> begin
true
end
| _ -> begin
false
end))

# 44 "FStar.TypeChecker.Common.fst"
let ___TProb____0 : prob  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) problem = (fun projectee -> (match (projectee) with
| TProb (_65_16) -> begin
_65_16
end))

# 45 "FStar.TypeChecker.Common.fst"
let ___CProb____0 : prob  ->  (FStar_Syntax_Syntax.comp, Prims.unit) problem = (fun projectee -> (match (projectee) with
| CProb (_65_19) -> begin
_65_19
end))

# 47 "FStar.TypeChecker.Common.fst"
type probs =
prob Prims.list

# 49 "FStar.TypeChecker.Common.fst"
type guard_formula =
| Trivial
| NonTrivial of FStar_Syntax_Syntax.formula

# 50 "FStar.TypeChecker.Common.fst"
let is_Trivial = (fun _discr_ -> (match (_discr_) with
| Trivial (_) -> begin
true
end
| _ -> begin
false
end))

# 51 "FStar.TypeChecker.Common.fst"
let is_NonTrivial = (fun _discr_ -> (match (_discr_) with
| NonTrivial (_) -> begin
true
end
| _ -> begin
false
end))

# 51 "FStar.TypeChecker.Common.fst"
let ___NonTrivial____0 : guard_formula  ->  FStar_Syntax_Syntax.formula = (fun projectee -> (match (projectee) with
| NonTrivial (_65_22) -> begin
_65_22
end))

# 53 "FStar.TypeChecker.Common.fst"
type deferred =
(Prims.string * prob) Prims.list

# 54 "FStar.TypeChecker.Common.fst"
type univ_ineq =
(FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)




