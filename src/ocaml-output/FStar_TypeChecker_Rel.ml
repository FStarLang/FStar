
open Prims

let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (

let uv = (FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(

let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k)))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((uv), (uv)))
end
| _55_37 -> begin
(

let args = (FStar_All.pipe_right binders (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder))
in (

let k' = (let _147_7 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _147_7))
in (

let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k')))) None r)
in (let _147_8 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((uv), (args)))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((_147_8), (uv))))))
end)))


type uvi =
| TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term)
| UNIV of (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe)


let is_TERM = (fun _discr_ -> (match (_discr_) with
| TERM (_) -> begin
true
end
| _ -> begin
false
end))


let is_UNIV = (fun _discr_ -> (match (_discr_) with
| UNIV (_) -> begin
true
end
| _ -> begin
false
end))


let ___TERM____0 = (fun projectee -> (match (projectee) with
| TERM (_55_43) -> begin
_55_43
end))


let ___UNIV____0 = (fun projectee -> (match (projectee) with
| UNIV (_55_46) -> begin
_55_46
end))


type worklist =
{attempting : FStar_TypeChecker_Common.probs; wl_deferred : (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list; ctr : Prims.int; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_TypeChecker_Env.env}


let is_Mkworklist : worklist  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkworklist"))))


type solution =
| Success of FStar_TypeChecker_Common.deferred
| Failed of (FStar_TypeChecker_Common.prob * Prims.string)


let is_Success = (fun _discr_ -> (match (_discr_) with
| Success (_) -> begin
true
end
| _ -> begin
false
end))


let is_Failed = (fun _discr_ -> (match (_discr_) with
| Failed (_) -> begin
true
end
| _ -> begin
false
end))


let ___Success____0 = (fun projectee -> (match (projectee) with
| Success (_55_56) -> begin
_55_56
end))


let ___Failed____0 = (fun projectee -> (match (projectee) with
| Failed (_55_59) -> begin
_55_59
end))


type variance =
| COVARIANT
| CONTRAVARIANT
| INVARIANT


let is_COVARIANT = (fun _discr_ -> (match (_discr_) with
| COVARIANT (_) -> begin
true
end
| _ -> begin
false
end))


let is_CONTRAVARIANT = (fun _discr_ -> (match (_discr_) with
| CONTRAVARIANT (_) -> begin
true
end
| _ -> begin
false
end))


let is_INVARIANT = (fun _discr_ -> (match (_discr_) with
| INVARIANT (_) -> begin
true
end
| _ -> begin
false
end))


type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem


type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem


type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun _55_1 -> (match (_55_1) with
| FStar_TypeChecker_Common.EQ -> begin
"="
end
| FStar_TypeChecker_Common.SUB -> begin
"<:"
end
| FStar_TypeChecker_Common.SUBINV -> begin
":>"
end))


let term_to_string = (fun env t -> (FStar_Syntax_Print.term_to_string t))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env _55_2 -> (match (_55_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _147_109 = (let _147_108 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _147_107 = (let _147_106 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _147_105 = (let _147_104 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _147_103 = (let _147_102 = (let _147_101 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _147_100 = (let _147_99 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _147_98 = (let _147_97 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _147_96 = (let _147_95 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_147_95)::[])
in (_147_97)::_147_96))
in (_147_99)::_147_98))
in (_147_101)::_147_100))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_147_102)
in (_147_104)::_147_103))
in (_147_106)::_147_105))
in (_147_108)::_147_107))
in (FStar_Util.format "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _147_109))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _147_111 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _147_110 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _147_111 (rel_to_string p.FStar_TypeChecker_Common.relation) _147_110)))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _55_3 -> (match (_55_3) with
| UNIV (u, t) -> begin
(

let x = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _147_116 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _147_116 FStar_Util.string_of_int))
end
in (let _147_117 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _147_117)))
end
| TERM ((u, _55_83), t) -> begin
(

let x = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _147_118 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _147_118 FStar_Util.string_of_int))
end
in (let _147_119 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _147_119)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _147_124 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _147_124 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (let _147_128 = (let _147_127 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _147_127 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _147_128 (FStar_String.concat ", "))))


let args_to_string = (fun args -> (let _147_131 = (FStar_All.pipe_right args (FStar_List.map (fun _55_96 -> (match (_55_96) with
| (x, _55_95) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _147_131 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = 0; defer_ok = true; smt_ok = true; tcenv = env})


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let _55_101 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _55_101.wl_deferred; ctr = _55_101.ctr; defer_ok = _55_101.defer_ok; smt_ok = smt_ok; tcenv = _55_101.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard = (fun env g -> (

let _55_107 = (empty_worklist env)
in (let _147_146 = (FStar_List.map Prims.snd g)
in {attempting = _147_146; wl_deferred = _55_107.wl_deferred; ctr = _55_107.ctr; defer_ok = false; smt_ok = _55_107.smt_ok; tcenv = _55_107.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let _55_112 = wl
in {attempting = _55_112.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = _55_112.ctr; defer_ok = _55_112.defer_ok; smt_ok = _55_112.smt_ok; tcenv = _55_112.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let _55_116 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _55_116.wl_deferred; ctr = _55_116.ctr; defer_ok = _55_116.defer_ok; smt_ok = _55_116.smt_ok; tcenv = _55_116.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (

let _55_121 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_163 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _147_163))
end else begin
()
end
in Failed (((prob), (reason)))))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun _55_4 -> (match (_55_4) with
| FStar_TypeChecker_Common.EQ -> begin
FStar_TypeChecker_Common.EQ
end
| FStar_TypeChecker_Common.SUB -> begin
FStar_TypeChecker_Common.SUBINV
end
| FStar_TypeChecker_Common.SUBINV -> begin
FStar_TypeChecker_Common.SUB
end))


let invert = (fun p -> (

let _55_128 = p
in {FStar_TypeChecker_Common.pid = _55_128.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _55_128.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_128.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_128.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_128.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_128.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_128.FStar_TypeChecker_Common.rank}))


let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _55_5 -> (match (_55_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _147_170 -> FStar_TypeChecker_Common.TProb (_147_170)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _147_171 -> FStar_TypeChecker_Common.CProb (_147_171)))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel _55_6 -> (match (_55_6) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun _55_7 -> (match (_55_7) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun _55_8 -> (match (_55_8) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun _55_9 -> (match (_55_9) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun _55_10 -> (match (_55_10) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun _55_11 -> (match (_55_11) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun _55_12 -> (match (_55_12) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _55_13 -> (match (_55_13) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _147_190 -> FStar_TypeChecker_Common.TProb (_147_190)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _147_191 -> FStar_TypeChecker_Common.CProb (_147_191)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))


let next_pid : Prims.unit  ->  Prims.int = (

let ctr = (FStar_ST.alloc 0)
in (fun _55_178 -> (match (()) with
| () -> begin
(

let _55_179 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))


let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _147_204 = (next_pid ())
in (let _147_203 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _147_204; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _147_203; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))


let new_problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _147_214 = (next_pid ())
in (let _147_213 = (let _147_212 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _147_212 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _147_214; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _147_213; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _147_221 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _147_221; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))


let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _147_233 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _147_232 = (prob_to_string env d)
in (let _147_231 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _147_233 _147_232 _147_231 s))))
end else begin
(

let d = (maybe_invert_p d)
in (

let rel = (match ((p_rel d)) with
| FStar_TypeChecker_Common.EQ -> begin
"equal to"
end
| FStar_TypeChecker_Common.SUB -> begin
"a subtype of"
end
| _55_215 -> begin
(FStar_All.failwith "impossible")
end)
in (

let _55_223 = (match (d) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(let _147_235 = (FStar_Syntax_Print.term_to_string tp.FStar_TypeChecker_Common.lhs)
in (let _147_234 = (FStar_Syntax_Print.term_to_string tp.FStar_TypeChecker_Common.rhs)
in ((_147_235), (_147_234))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _147_237 = (FStar_Syntax_Print.comp_to_string cp.FStar_TypeChecker_Common.lhs)
in (let _147_236 = (FStar_Syntax_Print.comp_to_string cp.FStar_TypeChecker_Common.rhs)
in ((_147_237), (_147_236))))
end)
in (match (_55_223) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)


let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _55_14 -> (match (_55_14) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| _55_233 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _55_236), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))


let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _55_15 -> (match (_55_15) with
| UNIV (_55_245) -> begin
None
end
| TERM ((u, _55_249), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun _55_16 -> (match (_55_16) with
| UNIV (u', t) -> begin
if (FStar_Unionfind.equivalent u u') then begin
Some (t)
end else begin
None
end
end
| _55_262 -> begin
None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _147_256 = (let _147_255 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _147_255))
in (FStar_Syntax_Subst.compress _147_256)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _147_261 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _147_261)))


let norm_arg = (fun env t -> (let _147_264 = (sn env (Prims.fst t))
in ((_147_264), ((Prims.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _55_273 -> (match (_55_273) with
| (x, imp) -> begin
(let _147_271 = (

let _55_274 = x
in (let _147_270 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_274.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_274.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_270}))
in ((_147_271), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _147_278 = (aux u)
in FStar_Syntax_Syntax.U_succ (_147_278))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _147_279 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_147_279))
end
| _55_286 -> begin
u
end)))
in (let _147_280 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _147_280))))


let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let base_and_refinement = (fun env wl t1 -> (

let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
if norm then begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end else begin
(match ((normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _55_306; FStar_Syntax_Syntax.pos = _55_304; FStar_Syntax_Syntax.vars = _55_302} -> begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end
| tt -> begin
(let _147_294 = (let _147_293 = (FStar_Syntax_Print.term_to_string tt)
in (let _147_292 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _147_293 _147_292)))
in (FStar_All.failwith _147_294))
end)
end
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
if norm then begin
((t1), (None))
end else begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (match ((let _147_295 = (FStar_Syntax_Subst.compress t1')
in _147_295.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_refine (_55_324) -> begin
(aux true t1')
end
| _55_327 -> begin
((t1), (None))
end))
end
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
((t1), (None))
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _147_298 = (let _147_297 = (FStar_Syntax_Print.term_to_string t1)
in (let _147_296 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _147_297 _147_296)))
in (FStar_All.failwith _147_298))
end))
in (let _147_299 = (whnf env t1)
in (aux false _147_299))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _147_304 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _147_304 Prims.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _147_307 = (FStar_Syntax_Syntax.null_bv t)
in ((_147_307), (FStar_Syntax_Util.t_true))))


let as_refinement = (fun env wl t -> (

let _55_373 = (base_and_refinement env wl t)
in (match (_55_373) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement = (fun _55_381 -> (match (_55_381) with
| (t_base, refopt) -> begin
(

let _55_389 = (match (refopt) with
| Some (y, phi) -> begin
((y), (phi))
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_55_389) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl _55_17 -> (match (_55_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _147_320 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _147_319 = (let _147_316 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _147_316))
in (let _147_318 = (let _147_317 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _147_317))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _147_320 _147_319 (rel_to_string p.FStar_TypeChecker_Common.relation) _147_318))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _147_323 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _147_322 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _147_321 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _147_323 _147_322 (rel_to_string p.FStar_TypeChecker_Common.relation) _147_321))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _147_329 = (let _147_328 = (let _147_327 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _55_402 -> (match (_55_402) with
| (_55_398, _55_400, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _147_327))
in (FStar_List.map (wl_prob_to_string wl) _147_328))
in (FStar_All.pipe_right _147_329 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let _55_421 = (match ((let _147_336 = (FStar_Syntax_Subst.compress k)
in _147_336.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if ((FStar_List.length bs) = (FStar_List.length ys)) then begin
(let _147_337 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (_147_337)))
end else begin
(

let _55_412 = (FStar_Syntax_Util.abs_formals t)
in (match (_55_412) with
| (ys', t) -> begin
(let _147_338 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t))), (_147_338)))
end))
end
end
| _55_414 -> begin
(let _147_340 = (let _147_339 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_147_339)))
in ((((ys), (t))), (_147_340)))
end)
in (match (_55_421) with
| ((ys, t), (xs, c)) -> begin
if ((FStar_List.length xs) <> (FStar_List.length ys)) then begin
(FStar_Syntax_Util.abs ys t (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))
end else begin
(

let c = (let _147_341 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp _147_341 c))
in (let _147_345 = (let _147_344 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _147_342 -> FStar_Util.Inl (_147_342)))
in (FStar_All.pipe_right _147_344 (fun _147_343 -> Some (_147_343))))
in (FStar_Syntax_Util.abs ys t _147_345)))
end
end)))


let solve_prob' : Prims.bool  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun resolve_ok prob logical_guard uvis wl -> (

let phi = (match (logical_guard) with
| None -> begin
FStar_Syntax_Util.t_true
end
| Some (phi) -> begin
phi
end)
in (

let _55_435 = (p_guard prob)
in (match (_55_435) with
| (_55_433, uv) -> begin
(

let _55_446 = (match ((let _147_356 = (FStar_Syntax_Subst.compress uv)
in _147_356.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi = (u_abs k bs phi)
in (

let _55_442 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _147_359 = (FStar_Util.string_of_int (p_pid prob))
in (let _147_358 = (FStar_Syntax_Print.term_to_string uv)
in (let _147_357 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _147_359 _147_358 _147_357))))
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi))))
end
| _55_445 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (

let _55_448 = (commit uvis)
in (

let _55_450 = wl
in {attempting = _55_450.attempting; wl_deferred = _55_450.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _55_450.defer_ok; smt_ok = _55_450.smt_ok; tcenv = _55_450.tcenv})))
end))))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> (

let _55_455 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _147_368 = (FStar_Util.string_of_int pid)
in (let _147_367 = (let _147_366 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _147_366 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _147_368 _147_367)))
end else begin
()
end
in (

let _55_457 = (commit sol)
in (

let _55_459 = wl
in {attempting = _55_459.attempting; wl_deferred = _55_459.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _55_459.defer_ok; smt_ok = _55_459.smt_ok; tcenv = _55_459.tcenv}))))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (

let conj_guard = (fun t g -> (match (((t), (g))) with
| (_55_469, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(let _147_381 = (FStar_Syntax_Util.mk_conj t f)
in Some (_147_381))
end))
in (

let _55_481 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _147_384 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _147_383 = (let _147_382 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _147_382 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _147_384 _147_383)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))


let rec occurs = (fun wl uk t -> (let _147_394 = (let _147_392 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _147_392 FStar_Util.set_elements))
in (FStar_All.pipe_right _147_394 (FStar_Util.for_some (fun _55_490 -> (match (_55_490) with
| (uv, _55_489) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))


let occurs_check = (fun env wl uk t -> (

let occurs_ok = (not ((occurs wl uk t)))
in (

let msg = if occurs_ok then begin
None
end else begin
(let _147_401 = (let _147_400 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _147_399 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _147_400 _147_399)))
in Some (_147_401))
end
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let _55_505 = (occurs_check env wl uk t)
in (match (_55_505) with
| (occurs_ok, msg) -> begin
(let _147_407 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (_147_407), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars = (fun v1 v2 -> (

let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set v1)
in (

let _55_523 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _55_515 _55_518 -> (match (((_55_515), (_55_518))) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _147_416 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _147_416)) then begin
((isect), (isect_set))
end else begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _147_417 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (_147_417)))
end else begin
((isect), (isect_set))
end)
end
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (_55_523) with
| (isect, _55_522) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _55_529 _55_533 -> (match (((_55_529), (_55_533))) with
| ((a, _55_528), (b, _55_532)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt = (fun env seen arg -> (

let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _55_543 -> (match (_55_543) with
| (b, _55_542) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some (((a), ((Prims.snd hd))))
end
end
| _55_545 -> begin
None
end)))


let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| (hd)::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(

let _55_554 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_432 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _147_432))
end else begin
()
end
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))


let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
((t), (uv), (k), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _55_568; FStar_Syntax_Syntax.pos = _55_566; FStar_Syntax_Syntax.vars = _55_564}, args) -> begin
((t), (uv), (k), (args))
end
| _55_578 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))


let destruct_flex_pattern = (fun env t -> (

let _55_585 = (destruct_flex_t t)
in (match (_55_585) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((((t), (uv), (k), (args))), (Some (vars)))
end
| _55_589 -> begin
((((t), (uv), (k), (args))), (None))
end)
end)))


type match_result =
| MisMatch of (FStar_Syntax_Syntax.delta_depth Prims.option * FStar_Syntax_Syntax.delta_depth Prims.option)
| HeadMatch
| FullMatch


let is_MisMatch = (fun _discr_ -> (match (_discr_) with
| MisMatch (_) -> begin
true
end
| _ -> begin
false
end))


let is_HeadMatch = (fun _discr_ -> (match (_discr_) with
| HeadMatch (_) -> begin
true
end
| _ -> begin
false
end))


let is_FullMatch = (fun _discr_ -> (match (_discr_) with
| FullMatch (_) -> begin
true
end
| _ -> begin
false
end))


let ___MisMatch____0 = (fun projectee -> (match (projectee) with
| MisMatch (_55_592) -> begin
_55_592
end))


let head_match : match_result  ->  match_result = (fun _55_18 -> (match (_55_18) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| _55_599 -> begin
HeadMatch
end))


let fv_delta_depth : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.delta_depth = (fun env fv -> (match (fv.FStar_Syntax_Syntax.fv_delta) with
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
if (env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr) then begin
d
end else begin
FStar_Syntax_Syntax.Delta_constant
end
end
| d -> begin
d
end))


let rec delta_depth_of_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth Prims.option = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
None
end
| (FStar_Syntax_Syntax.Tm_uinst (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) | (FStar_Syntax_Syntax.Tm_app (t, _)) | (FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}, _)) -> begin
(delta_depth_of_term env t)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
Some ((fv_delta_depth env fv))
end)))


let rec head_matches : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  match_result = (fun env t1 t2 -> (

let t1 = (FStar_Syntax_Util.unmeta t1)
in (

let t2 = (FStar_Syntax_Util.unmeta t2)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_name (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
if (FStar_Syntax_Syntax.bv_eq x y) then begin
FullMatch
end else begin
MisMatch (((None), (None)))
end
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
if (FStar_Syntax_Syntax.fv_eq f g) then begin
FullMatch
end else begin
MisMatch (((Some ((fv_delta_depth env f))), (Some ((fv_delta_depth env g)))))
end
end
| (FStar_Syntax_Syntax.Tm_uinst (f, _55_685), FStar_Syntax_Syntax.Tm_uinst (g, _55_690)) -> begin
(let _147_468 = (head_matches env f g)
in (FStar_All.pipe_right _147_468 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch (((None), (None)))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _55_701), FStar_Syntax_Syntax.Tm_uvar (uv', _55_706)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch (((None), (None)))
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_712), FStar_Syntax_Syntax.Tm_refine (y, _55_717)) -> begin
(let _147_469 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _147_469 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_723), _55_727) -> begin
(let _147_470 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _147_470 head_match))
end
| (_55_730, FStar_Syntax_Syntax.Tm_refine (x, _55_733)) -> begin
(let _147_471 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _147_471 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _55_753), FStar_Syntax_Syntax.Tm_app (head', _55_758)) -> begin
(let _147_472 = (head_matches env head head')
in (FStar_All.pipe_right _147_472 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head, _55_764), _55_768) -> begin
(let _147_473 = (head_matches env head t2)
in (FStar_All.pipe_right _147_473 head_match))
end
| (_55_771, FStar_Syntax_Syntax.Tm_app (head, _55_774)) -> begin
(let _147_474 = (head_matches env t1 head)
in (FStar_All.pipe_right _147_474 head_match))
end
| _55_779 -> begin
(let _147_477 = (let _147_476 = (delta_depth_of_term env t1)
in (let _147_475 = (delta_depth_of_term env t2)
in ((_147_476), (_147_475))))
in MisMatch (_147_477))
end))))


let head_matches_delta = (fun env wl t1 t2 -> (

let success = (fun d r t1 t2 -> ((r), (if (d > 0) then begin
Some (((t1), (t2)))
end else begin
None
end)))
in (

let fail = (fun r -> ((r), (None)))
in (

let rec aux = (fun n_delta t1 t2 -> (

let r = (head_matches env t1 t2)
in (match (r) with
| MisMatch (Some (d1), Some (d2)) when (d1 = d2) -> begin
(match ((FStar_TypeChecker_Common.decr_delta_depth d1)) with
| None -> begin
(fail r)
end
| Some (d) -> begin
(

let t1 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (

let t2 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (aux (n_delta + 1) t1 t2)))
end)
end
| (MisMatch (Some (FStar_Syntax_Syntax.Delta_equational), _)) | (MisMatch (_, Some (FStar_Syntax_Syntax.Delta_equational))) -> begin
(fail r)
end
| MisMatch (Some (d1), Some (d2)) -> begin
(

let d1_greater_than_d2 = (FStar_TypeChecker_Common.delta_depth_greater_than d1 d2)
in (

let _55_830 = if d1_greater_than_d2 then begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in ((t1'), (t2)))
end else begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (let _147_498 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in ((t1), (_147_498))))
end
in (match (_55_830) with
| (t1, t2) -> begin
(aux (n_delta + 1) t1 t2)
end)))
end
| MisMatch (_55_832) -> begin
(fail r)
end
| _55_835 -> begin
(success n_delta r t1 t2)
end)))
in (aux 0 t1 t2)))))


type tc =
| T of FStar_Syntax_Syntax.term
| C of FStar_Syntax_Syntax.comp


let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))


let is_C = (fun _discr_ -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))


let ___T____0 = (fun projectee -> (match (projectee) with
| T (_55_838) -> begin
_55_838
end))


let ___C____0 = (fun projectee -> (match (projectee) with
| C (_55_841) -> begin
_55_841
end))


type tcs =
tc Prims.list


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (match ((head_matches env t t')) with
| MisMatch (_55_848) -> begin
false
end
| _55_851 -> begin
true
end))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(

let rebuild = (fun args' -> (

let args = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((_55_861, imp), T (t)) -> begin
((t), (imp))
end
| _55_868 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), (args)))) None t.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _55_873 -> (match (_55_873) with
| (t, _55_872) -> begin
((None), (INVARIANT), (T (t)))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let fail = (fun _55_880 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (

let _55_883 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_55_883) with
| (bs, c) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs tcs -> (match (((bs), (tcs))) with
| (((x, imp))::bs, (T (t))::tcs) -> begin
(aux (((((

let _55_900 = x
in {FStar_Syntax_Syntax.ppname = _55_900.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_900.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp)))::out) bs tcs)
end
| ([], (C (c))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _55_908 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (

let rec decompose = (fun out _55_19 -> (match (_55_19) with
| [] -> begin
(FStar_List.rev ((((None), (COVARIANT), (C (c))))::out))
end
| (hd)::rest -> begin
(decompose ((((Some (hd)), (CONTRAVARIANT), (T ((Prims.fst hd).FStar_Syntax_Syntax.sort))))::out) rest)
end))
in (let _147_580 = (decompose [] bs)
in ((rebuild), (matches), (_147_580)))))
end)))
end
| _55_917 -> begin
(

let rebuild = (fun _55_20 -> (match (_55_20) with
| [] -> begin
t
end
| _55_921 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t -> true)), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _55_21 -> (match (_55_21) with
| T (t) -> begin
t
end
| _55_928 -> begin
(FStar_All.failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _55_22 -> (match (_55_22) with
| T (t) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _55_933 -> begin
(FStar_All.failwith "Impossible")
end))


let imitation_sub_probs = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope args q -> (match (q) with
| (_55_946, variance, T (ti)) -> begin
(

let k = (

let _55_954 = (FStar_Syntax_Util.type_u ())
in (match (_55_954) with
| (t, _55_953) -> begin
(let _147_602 = (new_uvar r scope t)
in (Prims.fst _147_602))
end))
in (

let _55_958 = (new_uvar r scope k)
in (match (_55_958) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| _55_961 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args)))) None r)
end)
in (let _147_605 = (let _147_604 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _147_603 -> FStar_TypeChecker_Common.TProb (_147_603)) _147_604))
in ((T (gi_xs)), (_147_605))))
end)))
end
| (_55_964, _55_966, C (_55_968)) -> begin
(FStar_All.failwith "impos")
end))
in (

let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs -> begin
(

let _55_1046 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti); FStar_Syntax_Syntax.tk = _55_986; FStar_Syntax_Syntax.pos = _55_984; FStar_Syntax_Syntax.vars = _55_982})) -> begin
(match ((sub_prob scope args ((bopt), (variance), (T (ti))))) with
| (T (gi_xs), prob) -> begin
(let _147_614 = (let _147_613 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _147_612 -> C (_147_612)) _147_613))
in ((_147_614), ((prob)::[])))
end
| _55_997 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti); FStar_Syntax_Syntax.tk = _55_1005; FStar_Syntax_Syntax.pos = _55_1003; FStar_Syntax_Syntax.vars = _55_1001})) -> begin
(match ((sub_prob scope args ((bopt), (variance), (T (ti))))) with
| (T (gi_xs), prob) -> begin
(let _147_617 = (let _147_616 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _147_615 -> C (_147_615)) _147_616))
in ((_147_617), ((prob)::[])))
end
| _55_1016 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_55_1018, _55_1020, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _55_1026; FStar_Syntax_Syntax.pos = _55_1024; FStar_Syntax_Syntax.vars = _55_1022})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((None), (INVARIANT), (T ((Prims.fst t)))))))
in (

let components = (((None), (COVARIANT), (T (c.FStar_Syntax_Syntax.result_typ))))::components
in (

let _55_1037 = (let _147_619 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _147_619 FStar_List.unzip))
in (match (_55_1037) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (let _147_624 = (let _147_623 = (let _147_620 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _147_620 un_T))
in (let _147_622 = (let _147_621 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _147_621 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _147_623; FStar_Syntax_Syntax.effect_args = _147_622; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _147_624))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| _55_1040 -> begin
(

let _55_1043 = (sub_prob scope args q)
in (match (_55_1043) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (_55_1046) with
| (tc, probs) -> begin
(

let _55_1059 = (match (q) with
| (Some (b), _55_1050, _55_1052) -> begin
(let _147_626 = (let _147_625 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_147_625)::args)
in ((Some (b)), ((b)::scope), (_147_626)))
end
| _55_1055 -> begin
((None), (scope), (args))
end)
in (match (_55_1059) with
| (bopt, scope, args) -> begin
(

let _55_1063 = (aux scope args qs)
in (match (_55_1063) with
| (sub_probs, tcs, f) -> begin
(

let f = (match (bopt) with
| None -> begin
(let _147_629 = (let _147_628 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_147_628)
in (FStar_Syntax_Util.mk_conj_l _147_629))
end
| Some (b) -> begin
(let _147_633 = (let _147_632 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _147_631 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_147_632)::_147_631))
in (FStar_Syntax_Util.mk_conj_l _147_633))
end)
in (((FStar_List.append probs sub_probs)), ((tc)::tcs), (f)))
end))
end))
end))
end))
in (aux scope ps qs))))))


let rec eq_tm : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t1 t2 -> (

let t1 = (FStar_Syntax_Subst.compress t1)
in (

let t2 = (FStar_Syntax_Subst.compress t2)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(FStar_Syntax_Syntax.fv_eq f g)
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(c = d)
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, _55_1091), FStar_Syntax_Syntax.Tm_uvar (u2, _55_1096)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _55_1110 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _55_1116 _55_1120 -> (match (((_55_1116), (_55_1120))) with
| ((a1, _55_1115), (a2, _55_1119)) -> begin
(eq_tm a1 a2)
end)) a1 a2)))


type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)


type im_or_proj_t =
(((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) * FStar_Syntax_Syntax.arg Prims.list * ((tc Prims.list  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list))


let rigid_rigid : Prims.int = 0


let flex_rigid_eq : Prims.int = 1


let flex_refine_inner : Prims.int = 2


let flex_refine : Prims.int = 3


let flex_rigid : Prims.int = 4


let rigid_flex : Prims.int = 5


let refine_flex : Prims.int = 6


let flex_flex : Prims.int = 7


let compress_tprob = (fun wl p -> (

let _55_1123 = p
in (let _147_655 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _147_654 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _55_1123.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _147_655; FStar_TypeChecker_Common.relation = _55_1123.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _147_654; FStar_TypeChecker_Common.element = _55_1123.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1123.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1123.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1123.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1123.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1123.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _147_661 = (compress_tprob wl p)
in (FStar_All.pipe_right _147_661 (fun _147_660 -> FStar_TypeChecker_Common.TProb (_147_660))))
end
| FStar_TypeChecker_Common.CProb (_55_1130) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (let _147_666 = (compress_prob wl pr)
in (FStar_All.pipe_right _147_666 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let _55_1140 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1140) with
| (lh, _55_1139) -> begin
(

let _55_1144 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1144) with
| (rh, _55_1143) -> begin
(

let _55_1200 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (_55_1146), FStar_Syntax_Syntax.Tm_uvar (_55_1149)) -> begin
((flex_flex), (tp))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (_55_1165), _55_1168) -> begin
(

let _55_1172 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1172) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((flex_rigid), (tp))
end
| _55_1175 -> begin
(

let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _147_668 = (

let _55_1177 = tp
in (let _147_667 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = _55_1177.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1177.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1177.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _147_667; FStar_TypeChecker_Common.element = _55_1177.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1177.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1177.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1177.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1177.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1177.FStar_TypeChecker_Common.rank}))
in ((rank), (_147_668))))
end)
end))
end
| (_55_1180, FStar_Syntax_Syntax.Tm_uvar (_55_1182)) -> begin
(

let _55_1187 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1187) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((rigid_flex), (tp))
end
| _55_1190 -> begin
(let _147_670 = (

let _55_1191 = tp
in (let _147_669 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = _55_1191.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _147_669; FStar_TypeChecker_Common.relation = _55_1191.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1191.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1191.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1191.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1191.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1191.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1191.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1191.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (_147_670)))
end)
end))
end
| (_55_1194, _55_1196) -> begin
((rigid_rigid), (tp))
end)
in (match (_55_1200) with
| (rank, tp) -> begin
(let _147_672 = (FStar_All.pipe_right (

let _55_1201 = tp
in {FStar_TypeChecker_Common.pid = _55_1201.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1201.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1201.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1201.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1201.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1201.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1201.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1201.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1201.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _147_671 -> FStar_TypeChecker_Common.TProb (_147_671)))
in ((rank), (_147_672)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _147_674 = (FStar_All.pipe_right (

let _55_1205 = cp
in {FStar_TypeChecker_Common.pid = _55_1205.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1205.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1205.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1205.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1205.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1205.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1205.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1205.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1205.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _147_673 -> FStar_TypeChecker_Common.CProb (_147_673)))
in ((rigid_rigid), (_147_674)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun _55_1212 probs -> (match (_55_1212) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
((min), (out), (min_rank))
end
| (hd)::tl -> begin
(

let _55_1220 = (rank wl hd)
in (match (_55_1220) with
| (rank, hd) -> begin
if (rank <= flex_rigid_eq) then begin
(match (min) with
| None -> begin
((Some (hd)), ((FStar_List.append out tl)), (rank))
end
| Some (m) -> begin
((Some (hd)), ((FStar_List.append out ((m)::tl))), (rank))
end)
end else begin
if (rank < min_rank) then begin
(match (min) with
| None -> begin
(aux ((rank), (Some (hd)), (out)) tl)
end
| Some (m) -> begin
(aux ((rank), (Some (hd)), ((m)::out)) tl)
end)
end else begin
(aux ((min_rank), (min), ((hd)::out)) tl)
end
end
end))
end)
end))
in (aux (((flex_flex + 1)), (None), ([])) wl.attempting)))


let is_flex_rigid : Prims.int  ->  Prims.bool = (fun rank -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))


let is_rigid_flex : Prims.int  ->  Prims.bool = (fun rank -> ((rigid_flex <= rank) && (rank <= refine_flex)))


type univ_eq_sol =
| UDeferred of worklist
| USolved of worklist
| UFailed of Prims.string


let is_UDeferred = (fun _discr_ -> (match (_discr_) with
| UDeferred (_) -> begin
true
end
| _ -> begin
false
end))


let is_USolved = (fun _discr_ -> (match (_discr_) with
| USolved (_) -> begin
true
end
| _ -> begin
false
end))


let is_UFailed = (fun _discr_ -> (match (_discr_) with
| UFailed (_) -> begin
true
end
| _ -> begin
false
end))


let ___UDeferred____0 = (fun projectee -> (match (projectee) with
| UDeferred (_55_1231) -> begin
_55_1231
end))


let ___USolved____0 = (fun projectee -> (match (projectee) with
| USolved (_55_1234) -> begin
_55_1234
end))


let ___UFailed____0 = (fun projectee -> (match (projectee) with
| UFailed (_55_1237) -> begin
_55_1237
end))


let rec solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (

let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (

let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (

let _55_1253 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_1253) with
| (k, _55_1252) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _55_1257 -> begin
false
end)
end)))))
end
| _55_1259 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (

let try_umax_components = (fun u1 u2 msg -> (match (((u1), (u2))) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
if ((FStar_List.length us1) = (FStar_List.length us2)) then begin
(

let rec aux = (fun wl us1 us2 -> (match (((us1), (us2))) with
| ((u1)::us1, (u2)::us2) -> begin
(match ((solve_universe_eq orig wl u1 u2)) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed -> begin
failed
end)
end
| _55_1284 -> begin
USolved (wl)
end))
in (aux wl us1 us2))
end else begin
(let _147_754 = (let _147_753 = (FStar_Syntax_Print.univ_to_string u1)
in (let _147_752 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _147_753 _147_752)))
in UFailed (_147_754))
end
end
| ((FStar_Syntax_Syntax.U_max (us), u')) | ((u', FStar_Syntax_Syntax.U_max (us))) -> begin
(

let rec aux = (fun wl us -> (match (us) with
| [] -> begin
USolved (wl)
end
| (u)::us -> begin
(match ((solve_universe_eq orig wl u u')) with
| USolved (wl) -> begin
(aux wl us)
end
| failed -> begin
failed
end)
end))
in (aux wl us))
end
| _55_1302 -> begin
(let _147_761 = (let _147_760 = (FStar_Syntax_Print.univ_to_string u1)
in (let _147_759 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _147_760 _147_759 msg)))
in UFailed (_147_761))
end))
in (match (((u1), (u2))) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) -> begin
if (x.FStar_Ident.idText = y.FStar_Ident.idText) then begin
USolved (wl)
end else begin
UFailed ("Incompatible universes")
end
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
USolved (wl)
end
| (FStar_Syntax_Syntax.U_succ (u1), FStar_Syntax_Syntax.U_succ (u2)) -> begin
(solve_universe_eq orig wl u1 u2)
end
| (FStar_Syntax_Syntax.U_unif (v1), FStar_Syntax_Syntax.U_unif (v2)) -> begin
if (FStar_Unionfind.equivalent v1 v2) then begin
USolved (wl)
end else begin
(

let wl = (extend_solution orig ((UNIV (((v1), (u2))))::[]) wl)
in USolved (wl))
end
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(

let u = (norm_univ wl u)
in if (occurs_univ v1 u) then begin
(let _147_764 = (let _147_763 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _147_762 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _147_763 _147_762)))
in (try_umax_components u1 u2 _147_764))
end else begin
(let _147_765 = (extend_solution orig ((UNIV (((v1), (u))))::[]) wl)
in USolved (_147_765))
end)
end
| ((FStar_Syntax_Syntax.U_max (_), _)) | ((_, FStar_Syntax_Syntax.U_max (_))) -> begin
if wl.defer_ok then begin
UDeferred (wl)
end else begin
(

let u1 = (norm_univ wl u1)
in (

let u2 = (norm_univ wl u2)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
USolved (wl)
end else begin
(try_umax_components u1 u2 "")
end))
end
end
| ((FStar_Syntax_Syntax.U_succ (_), FStar_Syntax_Syntax.U_zero)) | ((FStar_Syntax_Syntax.U_succ (_), FStar_Syntax_Syntax.U_name (_))) | ((FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ (_))) | ((FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name (_))) | ((FStar_Syntax_Syntax.U_name (_), FStar_Syntax_Syntax.U_succ (_))) | ((FStar_Syntax_Syntax.U_name (_), FStar_Syntax_Syntax.U_zero)) -> begin
UFailed ("Incompatible universes")
end))))))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> (

let _55_1399 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _147_811 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _147_811))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(

let probs = (

let _55_1406 = probs
in {attempting = tl; wl_deferred = _55_1406.wl_deferred; ctr = _55_1406.ctr; defer_ok = _55_1406.defer_ok; smt_ok = _55_1406.smt_ok; tcenv = _55_1406.tcenv})
in (match (hd) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
if (((not (probs.defer_ok)) && (flex_refine_inner <= rank)) && (rank <= flex_rigid)) then begin
(match ((solve_flex_rigid_join env tp probs)) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end)
end else begin
if (((not (probs.defer_ok)) && (rigid_flex <= rank)) && (rank <= refine_flex)) then begin
(match ((solve_rigid_flex_meet env tp probs)) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end)
end else begin
(solve_t' env (maybe_invert tp) probs)
end
end
end))
end
| (None, _55_1421, _55_1423) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _55_1427 -> begin
(

let _55_1436 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _55_1433 -> (match (_55_1433) with
| (c, _55_1430, _55_1432) -> begin
(c < probs.ctr)
end))))
in (match (_55_1436) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _147_814 = (FStar_List.map (fun _55_1442 -> (match (_55_1442) with
| (_55_1439, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in Success (_147_814))
end
| _55_1444 -> begin
(let _147_817 = (

let _55_1445 = probs
in (let _147_816 = (FStar_All.pipe_right attempt (FStar_List.map (fun _55_1452 -> (match (_55_1452) with
| (_55_1448, _55_1450, y) -> begin
y
end))))
in {attempting = _147_816; wl_deferred = rest; ctr = _55_1445.ctr; defer_ok = _55_1445.defer_ok; smt_ok = _55_1445.smt_ok; tcenv = _55_1445.tcenv}))
in (solve env _147_817))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _147_823 = (solve_prob orig None [] wl)
in (solve env _147_823))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (

let rec aux = (fun wl us1 us2 -> (match (((us1), (us2))) with
| ([], []) -> begin
USolved (wl)
end
| ((u1)::us1, (u2)::us2) -> begin
(match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed_or_deferred -> begin
failed_or_deferred
end)
end
| _55_1487 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t1 = (whnf env t1)
in (

let t2 = (whnf env t2)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _55_1495; FStar_Syntax_Syntax.pos = _55_1493; FStar_Syntax_Syntax.vars = _55_1491}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _55_1507; FStar_Syntax_Syntax.pos = _55_1505; FStar_Syntax_Syntax.vars = _55_1503}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (

let _55_1516 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _55_1531 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(

let _55_1536 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_839 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _147_839 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (

let _55_1541 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _147_843 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" _147_843))
end else begin
()
end
in (

let _55_1545 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1545) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let _55_1551 = (head_matches_delta env () t1 t2)
in (match (_55_1551) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (_55_1553) -> begin
None
end
| FullMatch -> begin
(match (ts) with
| None -> begin
Some (((t1), ([])))
end
| Some (t1, t2) -> begin
Some (((t1), ([])))
end)
end
| HeadMatch -> begin
(

let _55_1569 = (match (ts) with
| Some (t1, t2) -> begin
(let _147_849 = (FStar_Syntax_Subst.compress t1)
in (let _147_848 = (FStar_Syntax_Subst.compress t2)
in ((_147_849), (_147_848))))
end
| None -> begin
(let _147_851 = (FStar_Syntax_Subst.compress t1)
in (let _147_850 = (FStar_Syntax_Subst.compress t2)
in ((_147_851), (_147_850))))
end)
in (match (_55_1569) with
| (t1, t2) -> begin
(

let eq_prob = (fun t1 t2 -> (let _147_857 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _147_856 -> FStar_TypeChecker_Common.TProb (_147_856)) _147_857)))
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(let _147_864 = (let _147_863 = (let _147_860 = (let _147_859 = (let _147_858 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (_147_858)))
in FStar_Syntax_Syntax.Tm_refine (_147_859))
in (FStar_Syntax_Syntax.mk _147_860 None t1.FStar_Syntax_Syntax.pos))
in (let _147_862 = (let _147_861 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (_147_861)::[])
in ((_147_863), (_147_862))))
in Some (_147_864))
end
| (_55_1583, FStar_Syntax_Syntax.Tm_refine (x, _55_1586)) -> begin
(let _147_867 = (let _147_866 = (let _147_865 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (_147_865)::[])
in ((t1), (_147_866)))
in Some (_147_867))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_1592), _55_1596) -> begin
(let _147_870 = (let _147_869 = (let _147_868 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (_147_868)::[])
in ((t2), (_147_869)))
in Some (_147_870))
end
| _55_1599 -> begin
(

let _55_1603 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1603) with
| (head1, _55_1602) -> begin
(match ((let _147_871 = (FStar_Syntax_Util.un_uinst head1)
in _147_871.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _55_1609; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_unfoldable (i); FStar_Syntax_Syntax.fv_qual = _55_1605}) -> begin
(

let prev = if (i > 1) then begin
FStar_Syntax_Syntax.Delta_unfoldable ((i - 1))
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t1)
in (

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t2)
in (disjoin t1 t2))))
end
| _55_1616 -> begin
None
end)
end))
end))
end))
end)
end)))
in (

let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _55_1620) -> begin
(

let _55_1645 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _55_23 -> (match (_55_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(

let _55_1631 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1631) with
| (u', _55_1630) -> begin
(match ((let _147_873 = (whnf env u')
in _147_873.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _55_1634) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _55_1638 -> begin
false
end)
end))
end
| _55_1640 -> begin
false
end)
end
| _55_1642 -> begin
false
end))))
in (match (_55_1645) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun _55_1649 tps -> (match (_55_1649) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(match ((let _147_878 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound _147_878))) with
| Some (bound, sub) -> begin
(make_lower_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end)
end
| _55_1662 -> begin
None
end)
end))
in (match ((let _147_880 = (let _147_879 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((_147_879), ([])))
in (make_lower_bound _147_880 lower_bounds))) with
| None -> begin
(

let _55_1664 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No lower bounds\n")
end else begin
()
end
in None)
end
| Some (lhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in (

let _55_1674 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(

let wl' = (

let _55_1671 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _55_1671.wl_deferred; ctr = _55_1671.ctr; defer_ok = _55_1671.defer_ok; smt_ok = _55_1671.smt_ok; tcenv = _55_1671.tcenv})
in (let _147_881 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" _147_881)))
end else begin
()
end
in (match ((solve_t env eq_prob (

let _55_1676 = wl
in {attempting = sub_probs; wl_deferred = _55_1676.wl_deferred; ctr = _55_1676.ctr; defer_ok = _55_1676.defer_ok; smt_ok = _55_1676.smt_ok; tcenv = _55_1676.tcenv}))) with
| Success (_55_1679) -> begin
(

let wl = (

let _55_1681 = wl
in {attempting = rest; wl_deferred = _55_1681.wl_deferred; ctr = _55_1681.ctr; defer_ok = _55_1681.defer_ok; smt_ok = _55_1681.smt_ok; tcenv = _55_1681.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let _55_1687 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| _55_1690 -> begin
None
end)))
end))
end))
end
| _55_1692 -> begin
(FStar_All.failwith "Impossible: Not a rigid-flex")
end)))
end))))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (

let _55_1696 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _147_887 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _147_887))
end else begin
()
end
in (

let _55_1700 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1700) with
| (u, args) -> begin
(

let _55_1706 = ((0), (1), (2), (3), (4))
in (match (_55_1706) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(

let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (

let base_types_match = (fun t1 t2 -> (

let _55_1715 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1715) with
| (h1, args1) -> begin
(

let _55_1719 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_1719) with
| (h2, _55_1718) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _147_899 = (let _147_898 = (let _147_897 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _147_896 -> FStar_TypeChecker_Common.TProb (_147_896)) _147_897))
in (_147_898)::[])
in Some (_147_899))
end
end else begin
None
end
end
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
if (FStar_Syntax_Syntax.bv_eq a b) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _147_903 = (let _147_902 = (let _147_901 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _147_900 -> FStar_TypeChecker_Common.TProb (_147_900)) _147_901))
in (_147_902)::[])
in Some (_147_903))
end
end else begin
None
end
end
| _55_1731 -> begin
None
end)
end))
end)))
in (

let conjoin = (fun t1 t2 -> (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(

let m = (base_types_match x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(

let x = (FStar_Syntax_Syntax.freshen_bv x)
in (

let subst = (FStar_Syntax_Syntax.DB (((0), (x))))::[]
in (

let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (

let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let _147_910 = (let _147_909 = (let _147_908 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _147_908))
in ((_147_909), (m)))
in Some (_147_910))))))
end))
end
| (_55_1753, FStar_Syntax_Syntax.Tm_refine (y, _55_1756)) -> begin
(

let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some (((t2), (m)))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_1766), _55_1770) -> begin
(

let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some (((t1), (m)))
end))
end
| _55_1777 -> begin
(

let m = (base_types_match t1 t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some (((t1), (m)))
end))
end))
in (

let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _55_1785) -> begin
(

let _55_1810 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _55_24 -> (match (_55_24) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(

let _55_1796 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1796) with
| (u', _55_1795) -> begin
(match ((let _147_912 = (whnf env u')
in _147_912.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _55_1799) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _55_1803 -> begin
false
end)
end))
end
| _55_1805 -> begin
false
end)
end
| _55_1807 -> begin
false
end))))
in (match (_55_1810) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun _55_1814 tps -> (match (_55_1814) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(match ((let _147_917 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _147_917))) with
| Some (bound, sub) -> begin
(make_upper_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end)
end
| _55_1827 -> begin
None
end)
end))
in (match ((let _147_919 = (let _147_918 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((_147_918), ([])))
in (make_upper_bound _147_919 upper_bounds))) with
| None -> begin
(

let _55_1829 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in (

let _55_1839 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(

let wl' = (

let _55_1836 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _55_1836.wl_deferred; ctr = _55_1836.ctr; defer_ok = _55_1836.defer_ok; smt_ok = _55_1836.smt_ok; tcenv = _55_1836.tcenv})
in (let _147_920 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _147_920)))
end else begin
()
end
in (match ((solve_t env eq_prob (

let _55_1841 = wl
in {attempting = sub_probs; wl_deferred = _55_1841.wl_deferred; ctr = _55_1841.ctr; defer_ok = _55_1841.defer_ok; smt_ok = _55_1841.smt_ok; tcenv = _55_1841.tcenv}))) with
| Success (_55_1844) -> begin
(

let wl = (

let _55_1846 = wl
in {attempting = rest; wl_deferred = _55_1846.wl_deferred; ctr = _55_1846.ctr; defer_ok = _55_1846.defer_ok; smt_ok = _55_1846.smt_ok; tcenv = _55_1846.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let _55_1852 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _55_1855 -> begin
None
end)))
end))
end))
end
| _55_1857 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (

let rec aux = (fun scope env subst xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
(

let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (

let _55_1874 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_948 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _147_948))
end else begin
()
end
in (

let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl ((((rhs_prob)::[]), (formula))))))
end
| (((hd1, imp))::xs, ((hd2, imp'))::ys) when (imp = imp') -> begin
(

let hd1 = (

let _55_1888 = hd1
in (let _147_949 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1888.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1888.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_949}))
in (

let hd2 = (

let _55_1891 = hd2
in (let _147_950 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1891.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1891.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_950}))
in (

let prob = (let _147_953 = (let _147_952 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _147_952 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _147_951 -> FStar_TypeChecker_Common.TProb (_147_951)) _147_953))
in (

let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (

let subst = (let _147_954 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (FStar_Syntax_Syntax.DB (((0), (hd1))))::_147_954)
in (

let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux ((((hd1), (imp)))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi = (let _147_956 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _147_955 = (FStar_Syntax_Util.close_forall ((((hd1), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj _147_956 _147_955)))
in (

let _55_1903 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_958 = (FStar_Syntax_Print.term_to_string phi)
in (let _147_957 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _147_958 _147_957)))
end else begin
()
end
in FStar_Util.Inl ((((prob)::sub_probs), (phi)))))
end
| fail -> begin
fail
end)))))))
end
| _55_1907 -> begin
FStar_Util.Inr ("arity or argument-qualifier mismatch")
end))
in (

let scope = (p_scope orig)
in (match ((aux scope env [] bs1 bs2)) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _147_962 = (compress_tprob wl problem)
in (solve_t' env _147_962 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (

let _55_1935 = (head_matches_delta env wl t1 t2)
in (match (_55_1935) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (_55_1937), _55_1940) -> begin
(

let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _55_1953 -> begin
false
end))
in if (((may_relate head1) || (may_relate head2)) && wl.smt_ok) then begin
(

let guard = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end else begin
(

let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(

let x = (FStar_Syntax_Syntax.new_bv None t1)
in (let _147_991 = (let _147_990 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _147_990 t2))
in (FStar_Syntax_Util.mk_forall x _147_991)))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
in (let _147_992 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _147_992)))
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_55_1963, Some (t1, t2)) -> begin
(solve_t env (

let _55_1969 = problem
in {FStar_TypeChecker_Common.pid = _55_1969.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_1969.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_1969.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1969.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1969.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1969.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1969.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1969.FStar_TypeChecker_Common.rank}) wl)
end
| (_55_1972, None) -> begin
(

let _55_1975 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_996 = (FStar_Syntax_Print.term_to_string t1)
in (let _147_995 = (FStar_Syntax_Print.tag_of_term t1)
in (let _147_994 = (FStar_Syntax_Print.term_to_string t2)
in (let _147_993 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _147_996 _147_995 _147_994 _147_993)))))
end else begin
()
end
in (

let _55_1979 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1979) with
| (head1, args1) -> begin
(

let _55_1982 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_1982) with
| (head2, args2) -> begin
(

let nargs = (FStar_List.length args1)
in if (nargs <> (FStar_List.length args2)) then begin
(let _147_1001 = (let _147_1000 = (FStar_Syntax_Print.term_to_string head1)
in (let _147_999 = (args_to_string args1)
in (let _147_998 = (FStar_Syntax_Print.term_to_string head2)
in (let _147_997 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _147_1000 _147_999 _147_998 _147_997)))))
in (giveup env _147_1001 orig))
end else begin
if ((nargs = 0) || (eq_args args1 args2)) then begin
(match ((solve_maybe_uinsts env orig head1 head2 wl)) with
| USolved (wl) -> begin
(let _147_1002 = (solve_prob orig None [] wl)
in (solve env _147_1002))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(

let _55_1992 = (base_and_refinement env wl t1)
in (match (_55_1992) with
| (base1, refinement1) -> begin
(

let _55_1995 = (base_and_refinement env wl t2)
in (match (_55_1995) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (None, None) -> begin
(match ((solve_maybe_uinsts env orig head1 head2 wl)) with
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end
| USolved (wl) -> begin
(

let subprobs = (FStar_List.map2 (fun _55_2008 _55_2012 -> (match (((_55_2008), (_55_2012))) with
| ((a, _55_2007), (a', _55_2011)) -> begin
(let _147_1006 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _147_1005 -> FStar_TypeChecker_Common.TProb (_147_1005)) _147_1006))
end)) args1 args2)
in (

let formula = (let _147_1008 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _147_1008))
in (

let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _55_2018 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env (

let _55_2021 = problem
in {FStar_TypeChecker_Common.pid = _55_2021.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _55_2021.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _55_2021.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2021.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2021.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2021.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2021.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2021.FStar_TypeChecker_Common.rank}) wl)))
end)
end))
end))
end
end)
end))
end)))
end)
end)))
in (

let imitate = (fun orig env wl p -> (

let _55_2040 = p
in (match (_55_2040) with
| (((u, k), xs, c), ps, (h, _55_2037, qs)) -> begin
(

let xs = (sn_binders env xs)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _55_2046 = (imitation_sub_probs orig env xs ps qs)
in (match (_55_2046) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (let _147_1023 = (h gs_xs)
in (let _147_1022 = (let _147_1021 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _147_1019 -> FStar_Util.Inl (_147_1019)))
in (FStar_All.pipe_right _147_1021 (fun _147_1020 -> Some (_147_1020))))
in (FStar_Syntax_Util.abs xs _147_1023 _147_1022)))
in (

let _55_2048 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1030 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _147_1029 = (FStar_Syntax_Print.comp_to_string c)
in (let _147_1028 = (FStar_Syntax_Print.term_to_string im)
in (let _147_1027 = (FStar_Syntax_Print.tag_of_term im)
in (let _147_1026 = (let _147_1024 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _147_1024 (FStar_String.concat ", ")))
in (let _147_1025 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are %s, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" _147_1030 _147_1029 _147_1028 _147_1027 _147_1026 _147_1025)))))))
end else begin
()
end
in (

let wl = (solve_prob orig (Some (formula)) ((TERM (((((u), (k))), (im))))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (

let imitate' = (fun orig env wl _55_25 -> (match (_55_25) with
| None -> begin
(giveup env "unable to compute subterms" orig)
end
| Some (p) -> begin
(imitate orig env wl p)
end))
in (

let project = (fun orig env wl i p -> (

let _55_2074 = p
in (match (_55_2074) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _55_2079 = (FStar_List.nth ps i)
in (match (_55_2079) with
| (pi, _55_2078) -> begin
(

let _55_2083 = (FStar_List.nth xs i)
in (match (_55_2083) with
| (xi, _55_2082) -> begin
(

let rec gs = (fun k -> (

let _55_2088 = (FStar_Syntax_Util.arrow_formals k)
in (match (_55_2088) with
| (bs, k) -> begin
(

let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
(([]), ([]))
end
| ((a, _55_2096))::tl -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (

let _55_2102 = (new_uvar r xs k_a)
in (match (_55_2102) with
| (gi_xs, gi) -> begin
(

let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (

let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst = (FStar_Syntax_Syntax.NT (((a), (gi_xs))))::subst
in (

let _55_2108 = (aux subst tl)
in (match (_55_2108) with
| (gi_xs', gi_ps') -> begin
(let _147_1060 = (let _147_1057 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_147_1057)::gi_xs')
in (let _147_1059 = (let _147_1058 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_147_1058)::gi_ps')
in ((_147_1060), (_147_1059))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _147_1061 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _147_1061)) then begin
None
end else begin
(

let _55_2112 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_55_2112) with
| (g_xs, _55_2111) -> begin
(

let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (let _147_1066 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (let _147_1065 = (let _147_1064 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _147_1062 -> FStar_Util.Inl (_147_1062)))
in (FStar_All.pipe_right _147_1064 (fun _147_1063 -> Some (_147_1063))))
in (FStar_Syntax_Util.abs xs _147_1066 _147_1065)))
in (

let sub = (let _147_1072 = (let _147_1071 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _147_1070 = (let _147_1069 = (FStar_List.map (fun _55_2120 -> (match (_55_2120) with
| (_55_2116, _55_2118, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _147_1069))
in (mk_problem (p_scope orig) orig _147_1071 (p_rel orig) _147_1070 None "projection")))
in (FStar_All.pipe_left (fun _147_1067 -> FStar_TypeChecker_Common.TProb (_147_1067)) _147_1072))
in (

let _55_2122 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1074 = (FStar_Syntax_Print.term_to_string proj)
in (let _147_1073 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _147_1074 _147_1073)))
end else begin
()
end
in (

let wl = (let _147_1076 = (let _147_1075 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_147_1075))
in (solve_prob orig _147_1076 ((TERM (((u), (proj))))::[]) wl))
in (let _147_1078 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _147_1077 -> Some (_147_1077)) _147_1078)))))))
end))
end)
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun orig lhs t2 wl -> (

let _55_2136 = lhs
in (match (_55_2136) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let _55_2141 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (_55_2141) with
| (xs, c) -> begin
if ((FStar_List.length xs) = (FStar_List.length ps)) then begin
(let _147_1100 = (let _147_1099 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (_147_1099)))
in Some (_147_1100))
end else begin
(

let k_uv = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (match ((let _147_1106 = (let _147_1105 = (FStar_Syntax_Subst.compress k)
in _147_1105.FStar_Syntax_Syntax.n)
in ((_147_1106), (args)))) with
| (_55_2147, []) -> begin
(let _147_1108 = (let _147_1107 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_147_1107)))
in Some (_147_1108))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(

let _55_2164 = (FStar_Syntax_Util.head_and_args k)
in (match (_55_2164) with
| (uv, uv_args) -> begin
(match ((let _147_1109 = (FStar_Syntax_Subst.compress uv)
in _147_1109.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, _55_2167) -> begin
(match ((pat_vars env [] uv_args)) with
| None -> begin
None
end
| Some (scope) -> begin
(

let xs = (FStar_All.pipe_right args (FStar_List.map (fun _55_2173 -> (let _147_1115 = (let _147_1114 = (let _147_1113 = (let _147_1112 = (let _147_1111 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _147_1111 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _147_1112))
in (Prims.fst _147_1113))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) _147_1114))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _147_1115)))))
in (

let c = (let _147_1119 = (let _147_1118 = (let _147_1117 = (let _147_1116 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _147_1116 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _147_1117))
in (Prims.fst _147_1118))
in (FStar_Syntax_Syntax.mk_Total _147_1119))
in (

let k' = (FStar_Syntax_Util.arrow xs c)
in (

let uv_sol = (let _147_1125 = (let _147_1124 = (let _147_1123 = (let _147_1122 = (let _147_1121 = (let _147_1120 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _147_1120 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total _147_1121))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _147_1122))
in FStar_Util.Inl (_147_1123))
in Some (_147_1124))
in (FStar_Syntax_Util.abs scope k' _147_1125))
in (

let _55_2179 = (FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)))
in Some (((xs), (c))))))))
end)
end
| _55_2182 -> begin
None
end)
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs, c), _55_2188) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs)
in if (n_xs = n_args) then begin
(let _147_1127 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right _147_1127 (fun _147_1126 -> Some (_147_1126))))
end else begin
if (n_xs < n_args) then begin
(

let _55_2194 = (FStar_Util.first_N n_xs args)
in (match (_55_2194) with
| (args, rest) -> begin
(

let _55_2197 = (FStar_Syntax_Subst.open_comp xs c)
in (match (_55_2197) with
| (xs, c) -> begin
(let _147_1129 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt _147_1129 (fun _55_2200 -> (match (_55_2200) with
| (xs', c) -> begin
Some ((((FStar_List.append xs xs')), (c)))
end))))
end))
end))
end else begin
(

let _55_2203 = (FStar_Util.first_N n_args xs)
in (match (_55_2203) with
| (xs, rest) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) None k.FStar_Syntax_Syntax.pos)
in (let _147_1132 = (let _147_1130 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs _147_1130))
in (FStar_All.pipe_right _147_1132 (fun _147_1131 -> Some (_147_1131)))))
end))
end
end))
end
| _55_2206 -> begin
(let _147_1136 = (let _147_1135 = (FStar_Syntax_Print.uvar_to_string uv)
in (let _147_1134 = (FStar_Syntax_Print.term_to_string k)
in (let _147_1133 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" _147_1135 _147_1134 _147_1133))))
in (FStar_All.failwith _147_1136))
end))
in (let _147_1174 = (elim k_uv ps)
in (FStar_Util.bind_opt _147_1174 (fun _55_2209 -> (match (_55_2209) with
| (xs, c) -> begin
(let _147_1173 = (let _147_1172 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (_147_1172)))
in Some (_147_1173))
end))))))
end
end)))
in (

let rec imitate_or_project = (fun n stopt i -> if ((i >= n) || (FStar_Option.isNone stopt)) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
(

let st = (FStar_Option.get stopt)
in (

let tx = (FStar_Unionfind.new_transaction ())
in if (i = (- (1))) then begin
(match ((imitate orig env wl st)) with
| Failed (_55_2217) -> begin
(

let _55_2219 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + 1)))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(

let _55_2227 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + 1)))
end
| Some (sol) -> begin
sol
end)
end))
end)
in (

let check_head = (fun fvs1 t2 -> (

let _55_2237 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_2237) with
| (hd, _55_2236) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _55_2248 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(

let _55_2250 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1185 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _147_1185))
end else begin
()
end
in false)
end)
end)
end)))
in (

let imitate_ok = (fun t2 -> (

let fvs_hd = (let _147_1189 = (let _147_1188 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _147_1188 Prims.fst))
in (FStar_All.pipe_right _147_1189 FStar_Syntax_Free.names))
in if (FStar_Util.set_is_empty fvs_hd) then begin
(- (1))
end else begin
0
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(

let t1 = (sn env t1)
in (

let t2 = (sn env t2)
in (

let fvs1 = (FStar_Syntax_Free.names t1)
in (

let fvs2 = (FStar_Syntax_Free.names t2)
in (

let _55_2263 = (occurs_check env wl ((uv), (k_uv)) t2)
in (match (_55_2263) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _147_1191 = (let _147_1190 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _147_1190))
in (giveup_or_defer orig _147_1191))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _147_1192 = (subterms args_lhs)
in (imitate' orig env wl _147_1192))
end else begin
(

let _55_2264 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1195 = (FStar_Syntax_Print.term_to_string t1)
in (let _147_1194 = (names_to_string fvs1)
in (let _147_1193 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _147_1195 _147_1194 _147_1193))))
end else begin
()
end
in (

let sol = (match (vars) with
| [] -> begin
t2
end
| _55_2268 -> begin
(let _147_1196 = (sn_binders env vars)
in (u_abs k_uv _147_1196 t2))
end)
in (

let wl = (solve_prob orig None ((TERM (((((uv), (k_uv))), (sol))))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(

let _55_2271 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1199 = (FStar_Syntax_Print.term_to_string t1)
in (let _147_1198 = (names_to_string fvs1)
in (let _147_1197 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _147_1199 _147_1198 _147_1197))))
end else begin
()
end
in (let _147_1200 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _147_1200 (- (1)))))
end else begin
(giveup env "free-variable check failed on a non-redex" orig)
end
end
end
end
end))))))
end
| None -> begin
if wl.defer_ok then begin
(solve env (defer "not a pattern" orig wl))
end else begin
if (let _147_1201 = (FStar_Syntax_Free.names t1)
in (check_head _147_1201 t2)) then begin
(

let im_ok = (imitate_ok t2)
in (

let _55_2275 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1202 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _147_1202 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _147_1203 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _147_1203 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (

let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(

let force_quasi_pattern = (fun xs_opt _55_2287 -> (match (_55_2287) with
| (t, u, k, args) -> begin
(

let _55_2291 = (FStar_Syntax_Util.arrow_formals k)
in (match (_55_2291) with
| (all_formals, _55_2290) -> begin
(

let _55_2292 = ()
in (

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match (((formals), (args))) with
| ([], []) -> begin
(

let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _55_2305 -> (match (_55_2305) with
| (x, imp) -> begin
(let _147_1225 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_147_1225), (imp)))
end))))
in (

let pattern_vars = (FStar_List.rev pattern_vars)
in (

let kk = (

let _55_2311 = (FStar_Syntax_Util.type_u ())
in (match (_55_2311) with
| (t, _55_2310) -> begin
(let _147_1226 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _147_1226))
end))
in (

let _55_2315 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_55_2315) with
| (t', tm_u1) -> begin
(

let _55_2322 = (destruct_flex_t t')
in (match (_55_2322) with
| (_55_2317, u1, k1, _55_2321) -> begin
(

let sol = (let _147_1228 = (let _147_1227 = (u_abs k all_formals t')
in ((((u), (k))), (_147_1227)))
in TERM (_147_1228))
in (

let t_app = (FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args None t.FStar_Syntax_Syntax.pos)
in ((sol), (((t_app), (u1), (k1), (pat_args))))))
end))
end)))))
end
| ((formal)::formals, (hd)::tl) -> begin
(match ((pat_var_opt env pat_args hd)) with
| None -> begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end
| Some (y) -> begin
(

let maybe_pat = (match (xs_opt) with
| None -> begin
true
end
| Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _55_2341 -> (match (_55_2341) with
| (x, _55_2340) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in if (not (maybe_pat)) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(

let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in if (not ((FStar_Util.set_is_subset_of fvs pattern_var_set))) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(let _147_1230 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _147_1230 formals tl))
end)
end)
end)
end
| _55_2345 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _147_1231 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _147_1231 all_formals args))))
end))
end))
in (

let solve_both_pats = (fun wl _55_2352 _55_2357 r -> (match (((_55_2352), (_55_2357))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _147_1240 = (solve_prob orig None [] wl)
in (solve env _147_1240))
end else begin
(

let xs = (sn_binders env xs)
in (

let ys = (sn_binders env ys)
in (

let zs = (intersect_vars xs ys)
in (

let _55_2362 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1245 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _147_1244 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _147_1243 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (let _147_1242 = (FStar_Syntax_Print.term_to_string k1)
in (let _147_1241 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" _147_1245 _147_1244 _147_1243 _147_1242 _147_1241))))))
end else begin
()
end
in (

let _55_2375 = (

let _55_2367 = (FStar_Syntax_Util.type_u ())
in (match (_55_2367) with
| (t, _55_2366) -> begin
(

let _55_2371 = (new_uvar r zs t)
in (match (_55_2371) with
| (k, _55_2370) -> begin
(let _147_1251 = (let _147_1246 = (new_uvar r zs k)
in (FStar_All.pipe_left Prims.fst _147_1246))
in (let _147_1250 = (let _147_1247 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow xs _147_1247))
in (let _147_1249 = (let _147_1248 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow ys _147_1248))
in ((_147_1251), (_147_1250), (_147_1249)))))
end))
end))
in (match (_55_2375) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs u_zs)
in (

let _55_2379 = (occurs_check env wl ((u1), (k1)) sub1)
in (match (_55_2379) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(

let sol1 = TERM (((((u1), (k1))), (sub1)))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(

let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(

let sub2 = (u_abs knew2 ys u_zs)
in (

let _55_2385 = (occurs_check env wl ((u2), (k2)) sub2)
in (match (_55_2385) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(

let sol2 = TERM (((((u2), (k2))), (sub2)))
in (

let wl = (solve_prob orig None ((sol1)::(sol2)::[]) wl)
in (solve env wl)))
end
end)))
end)
end
end)))
end))))))
end
end))
in (

let solve_one_pat = (fun _55_2393 _55_2398 -> (match (((_55_2393), (_55_2398))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(

let _55_2399 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1257 = (FStar_Syntax_Print.term_to_string t1)
in (let _147_1256 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _147_1257 _147_1256)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(

let sub_probs = (FStar_List.map2 (fun _55_2404 _55_2408 -> (match (((_55_2404), (_55_2408))) with
| ((a, _55_2403), (t2, _55_2407)) -> begin
(let _147_1262 = (let _147_1260 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _147_1260 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _147_1262 (fun _147_1261 -> FStar_TypeChecker_Common.TProb (_147_1261))))
end)) xs args2)
in (

let guard = (let _147_1264 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _147_1264))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(

let t2 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t2)
in (

let _55_2418 = (occurs_check env wl ((u1), (k1)) t2)
in (match (_55_2418) with
| (occurs_ok, _55_2417) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(

let sol = (let _147_1266 = (let _147_1265 = (u_abs k1 xs t2)
in ((((u1), (k1))), (_147_1265)))
in TERM (_147_1266))
in (

let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(

let _55_2429 = (force_quasi_pattern (Some (xs)) ((t2), (u2), (k2), (args2)))
in (match (_55_2429) with
| (sol, (_55_2424, u2, k2, ys)) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (

let _55_2431 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _147_1267 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _147_1267))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _55_2436 -> begin
(giveup env "impossible" orig)
end)))
end))
end else begin
(giveup_or_defer orig "flex-flex constraint")
end
end)
end))))
end)
end))
in (

let _55_2441 = lhs
in (match (_55_2441) with
| (t1, u1, k1, args1) -> begin
(

let _55_2446 = rhs
in (match (_55_2446) with
| (t2, u2, k2, args2) -> begin
(

let maybe_pat_vars1 = (pat_vars env [] args1)
in (

let maybe_pat_vars2 = (pat_vars env [] args2)
in (

let r = t2.FStar_Syntax_Syntax.pos
in (match (((maybe_pat_vars1), (maybe_pat_vars2))) with
| (Some (xs), Some (ys)) -> begin
(solve_both_pats wl ((u1), (k1), (xs), (args1)) ((u2), (k2), (ys), (args2)) t2.FStar_Syntax_Syntax.pos)
end
| (Some (xs), None) -> begin
(solve_one_pat ((t1), (u1), (k1), (xs)) rhs)
end
| (None, Some (ys)) -> begin
(solve_one_pat ((t2), (u2), (k2), (ys)) lhs)
end
| _55_2464 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(

let _55_2468 = (force_quasi_pattern None ((t1), (u1), (k1), (args1)))
in (match (_55_2468) with
| (sol, _55_2467) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (

let _55_2470 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _147_1268 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _147_1268))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _55_2475 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (

let orig = FStar_TypeChecker_Common.TProb (problem)
in if (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs) then begin
(let _147_1269 = (solve_prob orig None [] wl)
in (solve env _147_1269))
end else begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _147_1270 = (solve_prob orig None [] wl)
in (solve env _147_1270))
end else begin
(

let _55_2479 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _147_1271 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _147_1271))
end else begin
()
end
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let match_num_binders = (fun _55_2484 _55_2487 -> (match (((_55_2484), (_55_2487))) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(

let curry = (fun n bs mk_cod -> (

let _55_2494 = (FStar_Util.first_N n bs)
in (match (_55_2494) with
| (bs, rest) -> begin
(let _147_1301 = (mk_cod rest)
in ((bs), (_147_1301)))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _147_1305 = (let _147_1302 = (mk_cod1 [])
in ((bs1), (_147_1302)))
in (let _147_1304 = (let _147_1303 = (mk_cod2 [])
in ((bs2), (_147_1303)))
in ((_147_1305), (_147_1304))))
end else begin
if (l1 > l2) then begin
(let _147_1308 = (curry l2 bs1 mk_cod1)
in (let _147_1307 = (let _147_1306 = (mk_cod2 [])
in ((bs2), (_147_1306)))
in ((_147_1308), (_147_1307))))
end else begin
(let _147_1311 = (let _147_1309 = (mk_cod1 [])
in ((bs1), (_147_1309)))
in (let _147_1310 = (curry l1 bs2 mk_cod2)
in ((_147_1311), (_147_1310))))
end
end)))
end))
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| ((FStar_Syntax_Syntax.Tm_bvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_bvar (_))) -> begin
(FStar_All.failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (FStar_Syntax_Syntax.Tm_type (u1), FStar_Syntax_Syntax.Tm_type (u2)) -> begin
(solve_one_universe_eq env orig u1 u2 wl)
end
| (FStar_Syntax_Syntax.Tm_arrow (bs1, c1), FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) -> begin
(

let mk_c = (fun c _55_26 -> (match (_55_26) with
| [] -> begin
c
end
| bs -> begin
(let _147_1316 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _147_1316))
end))
in (

let _55_2537 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (_55_2537) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (

let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (

let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (

let rel = if (FStar_Options.use_eq_at_higher_order ()) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in (let _147_1323 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _147_1322 -> FStar_TypeChecker_Common.CProb (_147_1322)) _147_1323)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l _55_27 -> (match (_55_27) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l)))) None t.FStar_Syntax_Syntax.pos)
end))
in (

let _55_2567 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (_55_2567) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _147_1338 = (let _147_1337 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _147_1336 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _147_1337 problem.FStar_TypeChecker_Common.relation _147_1336 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _147_1335 -> FStar_TypeChecker_Common.TProb (_147_1335)) _147_1338))))
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_55_2572), FStar_Syntax_Syntax.Tm_refine (_55_2575)) -> begin
(

let _55_2580 = (as_refinement env wl t1)
in (match (_55_2580) with
| (x1, phi1) -> begin
(

let _55_2583 = (as_refinement env wl t2)
in (match (_55_2583) with
| (x2, phi2) -> begin
(

let base_prob = (let _147_1340 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _147_1339 -> FStar_TypeChecker_Common.TProb (_147_1339)) _147_1340))
in (

let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (

let subst = (FStar_Syntax_Syntax.DB (((0), (x1))))::[]
in (

let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (

let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (

let env = (FStar_TypeChecker_Env.push_bv env x1)
in (

let mk_imp = (fun imp phi1 phi2 -> (let _147_1357 = (imp phi1 phi2)
in (FStar_All.pipe_right _147_1357 (guard_on_element problem x1))))
in (

let fallback = (fun _55_2595 -> (match (()) with
| () -> begin
(

let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (

let guard = (let _147_1360 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _147_1360 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(

let ref_prob = (let _147_1364 = (let _147_1363 = (let _147_1362 = (FStar_Syntax_Syntax.mk_binder x1)
in (_147_1362)::(p_scope orig))
in (mk_problem _147_1363 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _147_1361 -> FStar_TypeChecker_Common.TProb (_147_1361)) _147_1364))
in (match ((solve env (

let _55_2600 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _55_2600.ctr; defer_ok = false; smt_ok = _55_2600.smt_ok; tcenv = _55_2600.tcenv}))) with
| Failed (_55_2603) -> begin
(fallback ())
end
| Success (_55_2606) -> begin
(

let guard = (let _147_1367 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _147_1366 = (let _147_1365 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _147_1365 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _147_1367 _147_1366)))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (

let wl = (

let _55_2610 = wl
in {attempting = _55_2610.attempting; wl_deferred = _55_2610.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _55_2610.defer_ok; smt_ok = _55_2610.smt_ok; tcenv = _55_2610.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _147_1369 = (destruct_flex_t t1)
in (let _147_1368 = (destruct_flex_t t2)
in (flex_flex orig _147_1369 _147_1368)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _147_1370 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _147_1370 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in if (let _147_1371 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _147_1371)) then begin
(let _147_1374 = (FStar_All.pipe_left (fun _147_1372 -> FStar_TypeChecker_Common.TProb (_147_1372)) (

let _55_2755 = problem
in {FStar_TypeChecker_Common.pid = _55_2755.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2755.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _55_2755.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2755.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2755.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2755.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2755.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2755.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2755.FStar_TypeChecker_Common.rank}))
in (let _147_1373 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _147_1374 _147_1373 t2 wl)))
end else begin
(

let _55_2759 = (base_and_refinement env wl t2)
in (match (_55_2759) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _147_1377 = (FStar_All.pipe_left (fun _147_1375 -> FStar_TypeChecker_Common.TProb (_147_1375)) (

let _55_2761 = problem
in {FStar_TypeChecker_Common.pid = _55_2761.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2761.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _55_2761.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2761.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2761.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2761.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2761.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2761.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2761.FStar_TypeChecker_Common.rank}))
in (let _147_1376 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _147_1377 _147_1376 t_base wl)))
end
| Some (y, phi) -> begin
(

let y' = (

let _55_2767 = y
in {FStar_Syntax_Syntax.ppname = _55_2767.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_2767.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element problem y' phi)
in (

let base_prob = (let _147_1379 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _147_1378 -> FStar_TypeChecker_Common.TProb (_147_1378)) _147_1379))
in (

let guard = (let _147_1380 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _147_1380 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))))
end)
end))
end)
end
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
if wl.defer_ok then begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end else begin
(

let _55_2800 = (base_and_refinement env wl t1)
in (match (_55_2800) with
| (t_base, _55_2799) -> begin
(solve_t env (

let _55_2801 = problem
in {FStar_TypeChecker_Common.pid = _55_2801.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _55_2801.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2801.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2801.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2801.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2801.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2801.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2801.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_55_2804), _55_2807) -> begin
(

let t2 = (let _147_1381 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _147_1381))
in (solve_t env (

let _55_2810 = problem
in {FStar_TypeChecker_Common.pid = _55_2810.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2810.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_2810.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_2810.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2810.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2810.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2810.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2810.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2810.FStar_TypeChecker_Common.rank}) wl))
end
| (_55_2813, FStar_Syntax_Syntax.Tm_refine (_55_2815)) -> begin
(

let t1 = (let _147_1382 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _147_1382))
in (solve_t env (

let _55_2819 = problem
in {FStar_TypeChecker_Common.pid = _55_2819.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_2819.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_2819.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2819.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2819.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2819.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2819.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2819.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2819.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(

let maybe_eta = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_55_2836) -> begin
t
end
| _55_2839 -> begin
(FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
end))
in (let _147_1387 = (

let _55_2840 = problem
in (let _147_1386 = (maybe_eta t1)
in (let _147_1385 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _55_2840.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _147_1386; FStar_TypeChecker_Common.relation = _55_2840.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _147_1385; FStar_TypeChecker_Common.element = _55_2840.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2840.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2840.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2840.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2840.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2840.FStar_TypeChecker_Common.rank})))
in (solve_t env _147_1387 wl)))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(

let head1 = (let _147_1388 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _147_1388 Prims.fst))
in (

let head2 = (let _147_1389 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _147_1389 Prims.fst))
in if ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) then begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in if ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2)) then begin
(

let guard = if (eq_tm t1 t2) then begin
None
end else begin
(let _147_1391 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _147_1390 -> Some (_147_1390)) _147_1391))
end
in (let _147_1392 = (solve_prob orig guard [] wl)
in (solve env _147_1392)))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _55_2921, _55_2923), _55_2927) -> begin
(solve_t' env (

let _55_2929 = problem
in {FStar_TypeChecker_Common.pid = _55_2929.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_2929.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_2929.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2929.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2929.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2929.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2929.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2929.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2929.FStar_TypeChecker_Common.rank}) wl)
end
| (_55_2932, FStar_Syntax_Syntax.Tm_ascribed (t2, _55_2935, _55_2937)) -> begin
(solve_t' env (

let _55_2941 = problem
in {FStar_TypeChecker_Common.pid = _55_2941.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2941.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_2941.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_2941.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2941.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2941.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2941.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2941.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2941.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _147_1395 = (let _147_1394 = (FStar_Syntax_Print.tag_of_term t1)
in (let _147_1393 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _147_1394 _147_1393)))
in (FStar_All.failwith _147_1395))
end
| _55_2980 -> begin
(giveup env "head tag mismatch" orig)
end))))
end))
end)))))))))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (

let c1 = problem.FStar_TypeChecker_Common.lhs
in (

let c2 = problem.FStar_TypeChecker_Common.rhs
in (

let orig = FStar_TypeChecker_Common.CProb (problem)
in (

let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (

let solve_eq = (fun c1_comp c2_comp -> (

let _55_2997 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (

let sub_probs = (FStar_List.map2 (fun _55_3002 _55_3006 -> (match (((_55_3002), (_55_3006))) with
| ((a1, _55_3001), (a2, _55_3005)) -> begin
(let _147_1410 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _147_1409 -> FStar_TypeChecker_Common.TProb (_147_1409)) _147_1410))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (let _147_1412 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _147_1412))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in (

let solve_sub = (fun c1 edge c2 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(

let wp = (match (c1.FStar_Syntax_Syntax.effect_args) with
| ((wp1, _55_3018))::[] -> begin
wp1
end
| _55_3022 -> begin
(let _147_1420 = (let _147_1419 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _147_1419))
in (FStar_All.failwith _147_1420))
end)
in (

let c1 = (let _147_1423 = (let _147_1422 = (let _147_1421 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _147_1421))
in (_147_1422)::[])
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _147_1423; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2)))
end else begin
(

let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _55_28 -> (match (_55_28) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _55_3030 -> begin
false
end))))
in (

let _55_3051 = (match (((c1.FStar_Syntax_Syntax.effect_args), (c2.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, _55_3036))::_55_3033, ((wp2, _55_3043))::_55_3040) -> begin
((wp1), (wp2))
end
| _55_3048 -> begin
(let _147_1427 = (let _147_1426 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _147_1425 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _147_1426 _147_1425)))
in (FStar_All.failwith _147_1427))
end)
in (match (_55_3051) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _147_1428 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _147_1428 wl))
end else begin
(

let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let g = if is_null_wp_2 then begin
(

let _55_3053 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _147_1438 = (let _147_1437 = (let _147_1436 = (let _147_1430 = (let _147_1429 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_147_1429)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _147_1430 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _147_1435 = (let _147_1434 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _147_1433 = (let _147_1432 = (let _147_1431 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _147_1431))
in (_147_1432)::[])
in (_147_1434)::_147_1433))
in ((_147_1436), (_147_1435))))
in FStar_Syntax_Syntax.Tm_app (_147_1437))
in (FStar_Syntax_Syntax.mk _147_1438 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(let _147_1450 = (let _147_1449 = (let _147_1448 = (let _147_1440 = (let _147_1439 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_147_1439)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _147_1440 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (let _147_1447 = (let _147_1446 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _147_1445 = (let _147_1444 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _147_1443 = (let _147_1442 = (let _147_1441 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _147_1441))
in (_147_1442)::[])
in (_147_1444)::_147_1443))
in (_147_1446)::_147_1445))
in ((_147_1448), (_147_1447))))
in FStar_Syntax_Syntax.Tm_app (_147_1449))
in (FStar_Syntax_Syntax.mk _147_1450 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r))
end
in (

let base_prob = (let _147_1452 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _147_1451 -> FStar_TypeChecker_Common.TProb (_147_1451)) _147_1452))
in (

let wl = (let _147_1456 = (let _147_1455 = (let _147_1454 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _147_1454 g))
in (FStar_All.pipe_left (fun _147_1453 -> Some (_147_1453)) _147_1455))
in (solve_prob orig _147_1456 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end
end)))
end))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _147_1457 = (solve_prob orig None [] wl)
in (solve env _147_1457))
end else begin
(

let _55_3058 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1459 = (FStar_Syntax_Print.comp_to_string c1)
in (let _147_1458 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _147_1459 (rel_to_string problem.FStar_TypeChecker_Common.relation) _147_1458)))
end else begin
()
end
in (

let _55_3062 = (let _147_1461 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (let _147_1460 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((_147_1461), (_147_1460))))
in (match (_55_3062) with
| (c1, c2) -> begin
(match (((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.Total (t2)) when (FStar_Syntax_Util.non_informative t2) -> begin
(let _147_1462 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _147_1462 wl))
end
| (FStar_Syntax_Syntax.GTotal (_55_3069), FStar_Syntax_Syntax.Total (_55_3072)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _147_1463 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _147_1463 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _147_1465 = (

let _55_3100 = problem
in (let _147_1464 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _55_3100.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _147_1464; FStar_TypeChecker_Common.relation = _55_3100.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_3100.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_3100.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3100.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3100.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3100.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3100.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3100.FStar_TypeChecker_Common.rank}))
in (solve_c env _147_1465 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _147_1467 = (

let _55_3116 = problem
in (let _147_1466 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _55_3116.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_3116.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_3116.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _147_1466; FStar_TypeChecker_Common.element = _55_3116.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3116.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3116.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3116.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3116.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3116.FStar_TypeChecker_Common.rank}))
in (solve_c env _147_1467 wl))
end
| (FStar_Syntax_Syntax.Comp (_55_3119), FStar_Syntax_Syntax.Comp (_55_3122)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _147_1468 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _147_1468 wl))
end else begin
(

let c1_comp = (FStar_Syntax_Util.comp_to_comp_typ c1)
in (

let c2_comp = (FStar_Syntax_Util.comp_to_comp_typ c2)
in if ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(

let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (

let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (

let _55_3129 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
if (((FStar_Syntax_Util.is_ghost_effect c1.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c2.FStar_Syntax_Syntax.effect_name)) && (let _147_1469 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c2.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative _147_1469))) then begin
(

let edge = {FStar_TypeChecker_Env.msource = c1.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c2.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = (fun r t -> t)}
in (solve_sub c1 edge c2))
end else begin
(let _147_1474 = (let _147_1473 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _147_1472 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _147_1473 _147_1472)))
in (giveup env _147_1474 orig))
end
end
| Some (edge) -> begin
(solve_sub c1 edge c2)
end))))
end))
end
end)
end)))
end)))))))


let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _147_1478 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _55_3149 -> (match (_55_3149) with
| (_55_3139, _55_3141, u, _55_3144, _55_3146, _55_3148) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _147_1478 (FStar_String.concat ", "))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred))) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _55_3156 -> begin
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) then begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end else begin
"non-trivial"
end
end)
in (

let carry = (let _147_1484 = (FStar_List.map (fun _55_3164 -> (match (_55_3164) with
| (_55_3162, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _147_1484 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))


let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _55_3173; FStar_TypeChecker_Env.implicits = _55_3171} -> begin
true
end
| _55_3178 -> begin
false
end))


let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []}


let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _; FStar_TypeChecker_Env.univ_ineqs = _; FStar_TypeChecker_Env.implicits = _})) -> begin
g
end
| Some (g) -> begin
(

let f = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| _55_3196 -> begin
(FStar_All.failwith "impossible")
end)
in (let _147_1505 = (

let _55_3198 = g
in (let _147_1504 = (let _147_1503 = (let _147_1502 = (let _147_1496 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_1496)::[])
in (let _147_1501 = (let _147_1500 = (let _147_1499 = (let _147_1497 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _147_1497 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _147_1499 (fun _147_1498 -> FStar_Util.Inl (_147_1498))))
in Some (_147_1500))
in (FStar_Syntax_Util.abs _147_1502 f _147_1501)))
in (FStar_All.pipe_left (fun _147_1495 -> FStar_TypeChecker_Common.NonTrivial (_147_1495)) _147_1503))
in {FStar_TypeChecker_Env.guard_f = _147_1504; FStar_TypeChecker_Env.deferred = _55_3198.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3198.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3198.FStar_TypeChecker_Env.implicits}))
in Some (_147_1505)))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _55_3205 = g
in (let _147_1516 = (let _147_1515 = (let _147_1514 = (let _147_1513 = (let _147_1512 = (let _147_1511 = (FStar_Syntax_Syntax.as_arg e)
in (_147_1511)::[])
in ((f), (_147_1512)))
in FStar_Syntax_Syntax.Tm_app (_147_1513))
in (FStar_Syntax_Syntax.mk _147_1514 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _147_1510 -> FStar_TypeChecker_Common.NonTrivial (_147_1510)) _147_1515))
in {FStar_TypeChecker_Env.guard_f = _147_1516; FStar_TypeChecker_Env.deferred = _55_3205.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3205.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3205.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_55_3210) -> begin
(FStar_All.failwith "impossible")
end))


let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _147_1523 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_147_1523))
end))


let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _55_3228 -> begin
FStar_TypeChecker_Common.NonTrivial (t)
end))


let imp_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.Trivial, g) -> begin
g
end
| (g, FStar_TypeChecker_Common.Trivial) -> begin
FStar_TypeChecker_Common.Trivial
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let imp = (FStar_Syntax_Util.mk_imp f1 f2)
in (check_trivial imp))
end))


let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _147_1546 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _147_1546; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _55_3255 = g
in (let _147_1561 = (let _147_1560 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _147_1560 (fun _147_1559 -> FStar_TypeChecker_Common.NonTrivial (_147_1559))))
in {FStar_TypeChecker_Env.guard_f = _147_1561; FStar_TypeChecker_Env.deferred = _55_3255.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3255.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3255.FStar_TypeChecker_Env.implicits}))
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _147_1569 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _147_1568 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _147_1569 (rel_to_string rel) _147_1568)))
end else begin
"TOP"
end
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (let _147_1580 = (let _147_1579 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _147_1578 -> Some (_147_1578)) _147_1579))
in (FStar_Syntax_Syntax.new_bv _147_1580 t1))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (let _147_1584 = (let _147_1582 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _147_1581 -> Some (_147_1581)) _147_1582))
in (let _147_1583 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _147_1584 _147_1583)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (

let probs = if (FStar_Options.eager_inference ()) then begin
(

let _55_3275 = probs
in {attempting = _55_3275.attempting; wl_deferred = _55_3275.wl_deferred; ctr = _55_3275.ctr; defer_ok = false; smt_ok = _55_3275.smt_ok; tcenv = _55_3275.tcenv})
end else begin
probs
end
in (

let tx = (FStar_Unionfind.new_transaction ())
in (

let sol = (solve env probs)
in (match (sol) with
| Success (deferred) -> begin
(

let _55_3282 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(

let _55_3288 = (FStar_Unionfind.rollback tx)
in (

let _55_3290 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _147_1596 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _147_1596))
end else begin
()
end
in (err ((d), (s)))))
end)))))


let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _55_3297 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _147_1601 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _147_1601))
end else begin
()
end
in (

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (

let _55_3300 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _147_1602 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _147_1602))
end else begin
()
end
in (

let f = (match ((let _147_1603 = (FStar_Syntax_Util.unmeta f)
in _147_1603.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _55_3305 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (

let _55_3307 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _55_3307.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3307.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3307.FStar_TypeChecker_Env.implicits})))))
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _147_1615 = (let _147_1614 = (let _147_1613 = (let _147_1612 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _147_1612 (fun _147_1611 -> FStar_TypeChecker_Common.NonTrivial (_147_1611))))
in {FStar_TypeChecker_Env.guard_f = _147_1613; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _147_1614))
in (FStar_All.pipe_left (fun _147_1610 -> Some (_147_1610)) _147_1615))
end))


let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (

let _55_3318 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1623 = (FStar_Syntax_Print.term_to_string t1)
in (let _147_1622 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _147_1623 _147_1622)))
end else begin
()
end
in (

let prob = (let _147_1626 = (let _147_1625 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _147_1625))
in (FStar_All.pipe_left (fun _147_1624 -> FStar_TypeChecker_Common.TProb (_147_1624)) _147_1626))
in (

let g = (let _147_1628 = (solve_and_commit env (singleton env prob) (fun _55_3321 -> None))
in (FStar_All.pipe_left (with_guard env prob) _147_1628))
in g))))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _147_1638 = (let _147_1637 = (let _147_1636 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _147_1635 = (FStar_TypeChecker_Env.get_range env)
in ((_147_1636), (_147_1635))))
in FStar_Syntax_Syntax.Error (_147_1637))
in (Prims.raise _147_1638))
end
| Some (g) -> begin
(

let _55_3330 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1641 = (FStar_Syntax_Print.term_to_string t1)
in (let _147_1640 = (FStar_Syntax_Print.term_to_string t2)
in (let _147_1639 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _147_1641 _147_1640 _147_1639))))
end else begin
()
end
in g)
end))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 smt_ok -> (

let _55_3336 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1651 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _147_1650 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _147_1651 _147_1650)))
end else begin
()
end
in (

let _55_3340 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_55_3340) with
| (prob, x) -> begin
(

let g = (let _147_1653 = (solve_and_commit env (singleton' env prob smt_ok) (fun _55_3341 -> None))
in (FStar_All.pipe_left (with_guard env prob) _147_1653))
in (

let _55_3344 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _147_1657 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _147_1656 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _147_1655 = (let _147_1654 = (FStar_Util.must g)
in (guard_to_string env _147_1654))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _147_1657 _147_1656 _147_1655))))
end else begin
()
end
in (abstract_guard x g)))
end))))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env t1 t2 -> (let _147_1671 = (FStar_TypeChecker_Env.get_range env)
in (let _147_1670 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (FStar_TypeChecker_Errors.report _147_1671 _147_1670))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (

let _55_3355 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1679 = (FStar_Syntax_Print.comp_to_string c1)
in (let _147_1678 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _147_1679 _147_1678)))
end else begin
()
end
in (

let rel = if env.FStar_TypeChecker_Env.use_eq then begin
FStar_TypeChecker_Common.EQ
end else begin
FStar_TypeChecker_Common.SUB
end
in (

let prob = (let _147_1682 = (let _147_1681 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _147_1681 "sub_comp"))
in (FStar_All.pipe_left (fun _147_1680 -> FStar_TypeChecker_Common.CProb (_147_1680)) _147_1682))
in (let _147_1684 = (solve_and_commit env (singleton env prob) (fun _55_3359 -> None))
in (FStar_All.pipe_left (with_guard env prob) _147_1684))))))


let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (

let fail = (fun msg u1 u2 -> (

let _55_3368 = (FStar_Unionfind.rollback tx)
in (

let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _147_1702 = (let _147_1701 = (let _147_1700 = (let _147_1698 = (FStar_Syntax_Print.univ_to_string u1)
in (let _147_1697 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _147_1698 _147_1697 msg)))
in (let _147_1699 = (FStar_TypeChecker_Env.get_range env)
in ((_147_1700), (_147_1699))))
in FStar_Syntax_Syntax.Error (_147_1701))
in (Prims.raise _147_1702)))))
in (

let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
(((uv), ((u1)::[])))::[]
end
| (hd)::tl -> begin
(

let _55_3384 = hd
in (match (_55_3384) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
(((uv'), ((u1)::lower_bounds)))::tl
end else begin
(let _147_1709 = (insert uv u1 tl)
in (hd)::_147_1709)
end
end))
end))
in (

let rec group_by = (fun out ineqs -> (match (ineqs) with
| [] -> begin
Some (out)
end
| ((u1, u2))::rest -> begin
(

let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u2) with
| FStar_Syntax_Syntax.U_unif (uv) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
(group_by out rest)
end else begin
(let _147_1714 = (insert uv u1 out)
in (group_by _147_1714 rest))
end)
end
| _55_3399 -> begin
None
end))
end))
in (

let ad_hoc_fallback = (fun _55_3401 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _55_3404 -> begin
(

let wl = (

let _55_3405 = (empty_worklist env)
in {attempting = _55_3405.attempting; wl_deferred = _55_3405.wl_deferred; ctr = _55_3405.ctr; defer_ok = true; smt_ok = _55_3405.smt_ok; tcenv = _55_3405.tcenv})
in (FStar_All.pipe_right ineqs (FStar_List.iter (fun _55_3410 -> (match (_55_3410) with
| (u1, u2) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _55_3415 -> begin
(match ((solve_universe_eq (- (1)) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(

let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _55_3425 -> begin
(u1)::[]
end)
in (

let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _55_3430 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _55_29 -> (match (_55_29) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(

let _55_3437 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_3437) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (

let _55_3441 = (FStar_Syntax_Util.univ_kernel u')
in (match (_55_3441) with
| (k_u', n') -> begin
((FStar_Syntax_Util.eq_univs k_u k_u') && (n <= n'))
end)))))
end))
end)))) then begin
()
end else begin
(fail None u1 u2)
end))
end
| USolved (_55_3443) -> begin
()
end)
end)))
end)))))
end)
end))
in (match ((group_by [] ineqs)) with
| Some (groups) -> begin
(

let wl = (

let _55_3447 = (empty_worklist env)
in {attempting = _55_3447.attempting; wl_deferred = _55_3447.wl_deferred; ctr = _55_3447.ctr; defer_ok = false; smt_ok = _55_3447.smt_ok; tcenv = _55_3447.tcenv})
in (

let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| ((u, lower_bounds))::groups -> begin
(match ((solve_universe_eq (- (1)) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| _55_3462 -> begin
(ad_hoc_fallback ())
end)
end))
in (solve_all_groups wl groups)))
end
| None -> begin
(ad_hoc_fallback ())
end))))))


let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun env ineqs -> (

let tx = (FStar_Unionfind.new_transaction ())
in (

let _55_3467 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail = (fun _55_3474 -> (match (_55_3474) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error (((msg), ((p_loc d)))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (

let _55_3477 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _147_1735 = (wl_to_string wl)
in (let _147_1734 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _147_1735 _147_1734)))
end else begin
()
end
in (

let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(

let _55_3481 = g
in {FStar_TypeChecker_Env.guard_f = _55_3481.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _55_3481.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3481.FStar_TypeChecker_Env.implicits})
end
| _55_3484 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (

let _55_3486 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (

let _55_3488 = g
in {FStar_TypeChecker_Env.guard_f = _55_3488.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3488.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _55_3488.FStar_TypeChecker_Env.implicits})))))))


let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun use_env_range_msg env g -> (

let g = (solve_deferred_constraints env g)
in (

let _55_3503 = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(

let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(

let _55_3501 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1752 = (FStar_TypeChecker_Env.get_range env)
in (let _147_1751 = (let _147_1750 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _147_1750))
in (FStar_TypeChecker_Errors.diag _147_1752 _147_1751)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc))
end))
end)
end
in (

let _55_3505 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _55_3505.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3505.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3505.FStar_TypeChecker_Env.implicits}))))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (discharge_guard' None env g))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (

let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _55_3514 -> begin
false
end))
in (

let rec until_fixpoint = (fun _55_3518 implicits -> (match (_55_3518) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
if (not (changed)) then begin
out
end else begin
(until_fixpoint (([]), (false)) out)
end
end
| (hd)::tl -> begin
(

let _55_3531 = hd
in (match (_55_3531) with
| (_55_3525, env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint (((hd)::out), (changed)) tl)
end else begin
(

let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (

let _55_3534 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _147_1768 = (FStar_Syntax_Print.uvar_to_string u)
in (let _147_1767 = (FStar_Syntax_Print.term_to_string tm)
in (let _147_1766 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _147_1768 _147_1767 _147_1766))))
end else begin
()
end
in (

let _55_3543 = (env.FStar_TypeChecker_Env.type_of (

let _55_3536 = env
in {FStar_TypeChecker_Env.solver = _55_3536.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _55_3536.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _55_3536.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _55_3536.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _55_3536.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _55_3536.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _55_3536.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _55_3536.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _55_3536.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _55_3536.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _55_3536.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _55_3536.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _55_3536.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _55_3536.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _55_3536.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _55_3536.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _55_3536.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _55_3536.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _55_3536.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _55_3536.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _55_3536.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_55_3543) with
| (_55_3539, _55_3541, g) -> begin
(

let g = if env.FStar_TypeChecker_Env.is_pattern then begin
(

let _55_3544 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _55_3544.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3544.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3544.FStar_TypeChecker_Env.implicits})
end else begin
g
end
in (

let g' = (discharge_guard' (Some ((fun _55_3547 -> (match (()) with
| () -> begin
(FStar_Syntax_Print.term_to_string tm)
end)))) env g)
in (until_fixpoint (((FStar_List.append g'.FStar_TypeChecker_Env.implicits out)), (true)) tl)))
end)))))
end
end))
end)
end))
in (

let _55_3549 = g
in (let _147_1772 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _55_3549.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3549.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3549.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _147_1772})))))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g = (let _147_1777 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _147_1777 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _147_1778 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _147_1778))
end
| ((reason, _55_3559, _55_3561, e, t, r))::_55_3556 -> begin
(let _147_1781 = (let _147_1780 = (FStar_Syntax_Print.term_to_string t)
in (let _147_1779 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" _147_1780 _147_1779 reason)))
in (FStar_TypeChecker_Errors.report r _147_1781))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let _55_3569 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _55_3569.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3569.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (((u1), (u2)))::[]; FStar_TypeChecker_Env.implicits = _55_3569.FStar_TypeChecker_Env.implicits}))




