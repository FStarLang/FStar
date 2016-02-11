
open Prims
# 25 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

type rel =
| EQ
| SUB
| SUBINV

# 26 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

let is_EQ = (fun _discr_ -> (match (_discr_) with
| EQ (_) -> begin
true
end
| _ -> begin
false
end))

# 27 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

let is_SUB = (fun _discr_ -> (match (_discr_) with
| SUB (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

let is_SUBINV = (fun _discr_ -> (match (_discr_) with
| SUBINV (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

type ('a, 'b) problem =
{pid : Prims.int; lhs : 'a; relation : rel; rhs : 'a; element : 'b Prims.option; logical_guard : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term); scope : FStar_Syntax_Syntax.binders; reason : Prims.string Prims.list; loc : FStar_Range.range; rank : Prims.int Prims.option}

# 30 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

let is_Mkproblem = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkproblem"))))

# 43 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

type prob =
| TProb of (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) problem
| CProb of (FStar_Syntax_Syntax.comp, Prims.unit) problem

# 44 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

let is_TProb = (fun _discr_ -> (match (_discr_) with
| TProb (_) -> begin
true
end
| _ -> begin
false
end))

# 45 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

let is_CProb = (fun _discr_ -> (match (_discr_) with
| CProb (_) -> begin
true
end
| _ -> begin
false
end))

# 44 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

let ___TProb____0 : prob  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) problem = (fun projectee -> (match (projectee) with
| TProb (_81_16) -> begin
_81_16
end))

# 45 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

let ___CProb____0 : prob  ->  (FStar_Syntax_Syntax.comp, Prims.unit) problem = (fun projectee -> (match (projectee) with
| CProb (_81_19) -> begin
_81_19
end))

# 47 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

type probs =
prob Prims.list

# 49 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

type guard_formula =
| Trivial
| NonTrivial of FStar_Syntax_Syntax.formula

# 50 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

let is_Trivial = (fun _discr_ -> (match (_discr_) with
| Trivial (_) -> begin
true
end
| _ -> begin
false
end))

# 51 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

let is_NonTrivial = (fun _discr_ -> (match (_discr_) with
| NonTrivial (_) -> begin
true
end
| _ -> begin
false
end))

# 51 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

let ___NonTrivial____0 : guard_formula  ->  FStar_Syntax_Syntax.formula = (fun projectee -> (match (projectee) with
| NonTrivial (_81_22) -> begin
_81_22
end))

# 53 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

type deferred =
(Prims.string * prob) Prims.list

# 54 "C:\\Users\\nswamy\\workspace\\FStar\\src\\typechecker\\common.fs"

type univ_ineq =
(FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)




