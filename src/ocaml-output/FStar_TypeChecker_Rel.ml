
open Prims

let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (

let uv = (FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(

let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (uv, uv))
end
| _55_38 -> begin
(

let args = (FStar_All.pipe_right binders (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder))
in (

let k' = (let _145_7 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _145_7))
in (

let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k'))) None r)
in (let _145_8 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((uv, args))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (_145_8, uv)))))
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
| TERM (_55_44) -> begin
_55_44
end))


let ___UNIV____0 = (fun projectee -> (match (projectee) with
| UNIV (_55_47) -> begin
_55_47
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
| Success (_55_57) -> begin
_55_57
end))


let ___Failed____0 = (fun projectee -> (match (projectee) with
| Failed (_55_60) -> begin
_55_60
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
(let _145_107 = (let _145_106 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _145_105 = (let _145_104 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _145_103 = (let _145_102 = (let _145_101 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _145_100 = (let _145_99 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _145_98 = (let _145_97 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _145_96 = (let _145_95 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_145_95)::[])
in (_145_97)::_145_96))
in (_145_99)::_145_98))
in (_145_101)::_145_100))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_145_102)
in (_145_104)::_145_103))
in (_145_106)::_145_105))
in (FStar_Util.format "\t%s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _145_107))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _145_109 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _145_108 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _145_109 (rel_to_string p.FStar_TypeChecker_Common.relation) _145_108)))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _55_3 -> (match (_55_3) with
| UNIV (u, t) -> begin
(

let x = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _145_114 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _145_114 FStar_Util.string_of_int))
end
in (let _145_115 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _145_115)))
end
| TERM ((u, _55_84), t) -> begin
(

let x = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _145_116 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _145_116 FStar_Util.string_of_int))
end
in (let _145_117 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _145_117)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _145_122 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _145_122 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (let _145_126 = (let _145_125 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _145_125 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _145_126 (FStar_String.concat ", "))))


let args_to_string = (fun args -> (let _145_129 = (FStar_All.pipe_right args (FStar_List.map (fun _55_97 -> (match (_55_97) with
| (x, _55_96) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _145_129 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = 0; defer_ok = true; smt_ok = true; tcenv = env})


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (

let _55_101 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _55_101.wl_deferred; ctr = _55_101.ctr; defer_ok = _55_101.defer_ok; smt_ok = _55_101.smt_ok; tcenv = _55_101.tcenv}))


let wl_of_guard = (fun env g -> (

let _55_105 = (empty_worklist env)
in (let _145_138 = (FStar_List.map Prims.snd g)
in {attempting = _145_138; wl_deferred = _55_105.wl_deferred; ctr = _55_105.ctr; defer_ok = false; smt_ok = _55_105.smt_ok; tcenv = _55_105.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let _55_110 = wl
in {attempting = _55_110.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; ctr = _55_110.ctr; defer_ok = _55_110.defer_ok; smt_ok = _55_110.smt_ok; tcenv = _55_110.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let _55_114 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _55_114.wl_deferred; ctr = _55_114.ctr; defer_ok = _55_114.defer_ok; smt_ok = _55_114.smt_ok; tcenv = _55_114.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (

let _55_119 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_155 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _145_155))
end else begin
()
end
in Failed ((prob, reason))))


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

let _55_126 = p
in {FStar_TypeChecker_Common.pid = _55_126.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _55_126.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_126.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_126.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_126.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_126.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_126.FStar_TypeChecker_Common.rank}))


let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _55_5 -> (match (_55_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _145_162 -> FStar_TypeChecker_Common.TProb (_145_162)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _145_163 -> FStar_TypeChecker_Common.CProb (_145_163)))
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
(FStar_All.pipe_left (fun _145_182 -> FStar_TypeChecker_Common.TProb (_145_182)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _145_183 -> FStar_TypeChecker_Common.CProb (_145_183)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))


let next_pid : Prims.unit  ->  Prims.int = (

let ctr = (FStar_ST.alloc 0)
in (fun _55_176 -> (match (()) with
| () -> begin
(

let _55_177 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))


let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _145_196 = (next_pid ())
in (let _145_195 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _145_196; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _145_195; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))


let new_problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _145_206 = (next_pid ())
in (let _145_205 = (let _145_204 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _145_204 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _145_206; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _145_205; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _145_213 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _145_213; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))


let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((x, e)))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _145_225 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _145_224 = (prob_to_string env d)
in (let _145_223 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _145_225 _145_224 _145_223 s))))
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
| _55_213 -> begin
(FStar_All.failwith "impossible")
end)
in (

let _55_221 = (match (d) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(let _145_227 = (FStar_Syntax_Print.term_to_string tp.FStar_TypeChecker_Common.lhs)
in (let _145_226 = (FStar_Syntax_Print.term_to_string tp.FStar_TypeChecker_Common.rhs)
in (_145_227, _145_226)))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _145_229 = (FStar_Syntax_Print.comp_to_string cp.FStar_TypeChecker_Common.lhs)
in (let _145_228 = (FStar_Syntax_Print.comp_to_string cp.FStar_TypeChecker_Common.rhs)
in (_145_229, _145_228)))
end)
in (match (_55_221) with
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
| _55_231 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _55_234), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))


let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _55_15 -> (match (_55_15) with
| UNIV (_55_243) -> begin
None
end
| TERM ((u, _55_247), t) -> begin
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
| _55_260 -> begin
None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _145_248 = (let _145_247 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _145_247))
in (FStar_Syntax_Subst.compress _145_248)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _145_253 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _145_253)))


let norm_arg = (fun env t -> (let _145_256 = (sn env (Prims.fst t))
in (_145_256, (Prims.snd t))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _55_271 -> (match (_55_271) with
| (x, imp) -> begin
(let _145_263 = (

let _55_272 = x
in (let _145_262 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_272.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_272.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_262}))
in (_145_263, imp))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _145_270 = (aux u)
in FStar_Syntax_Syntax.U_succ (_145_270))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _145_271 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_145_271))
end
| _55_284 -> begin
u
end)))
in (let _145_272 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _145_272))))


let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let base_and_refinement = (fun env wl t1 -> (

let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
if norm then begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end else begin
(match ((normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _55_304; FStar_Syntax_Syntax.pos = _55_302; FStar_Syntax_Syntax.vars = _55_300} -> begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _145_286 = (let _145_285 = (FStar_Syntax_Print.term_to_string tt)
in (let _145_284 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _145_285 _145_284)))
in (FStar_All.failwith _145_286))
end)
end
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
if norm then begin
(t1, None)
end else begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (match ((let _145_287 = (FStar_Syntax_Subst.compress t1')
in _145_287.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_refine (_55_322) -> begin
(aux true t1')
end
| _55_325 -> begin
(t1, None)
end))
end
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
(t1, None)
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _145_290 = (let _145_289 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_288 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _145_289 _145_288)))
in (FStar_All.failwith _145_290))
end))
in (let _145_291 = (whnf env t1)
in (aux false _145_291))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _145_296 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _145_296 Prims.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _145_299 = (FStar_Syntax_Syntax.null_bv t)
in (_145_299, FStar_Syntax_Util.t_true)))


let as_refinement = (fun env wl t -> (

let _55_371 = (base_and_refinement env wl t)
in (match (_55_371) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
(x, phi)
end)
end)))


let force_refinement = (fun _55_379 -> (match (_55_379) with
| (t_base, refopt) -> begin
(

let _55_387 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_55_387) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((y, phi))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl _55_17 -> (match (_55_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _145_312 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _145_311 = (let _145_308 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _145_308))
in (let _145_310 = (let _145_309 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _145_309))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _145_312 _145_311 (rel_to_string p.FStar_TypeChecker_Common.relation) _145_310))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _145_315 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _145_314 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _145_313 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _145_315 _145_314 (rel_to_string p.FStar_TypeChecker_Common.relation) _145_313))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _145_321 = (let _145_320 = (let _145_319 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _55_400 -> (match (_55_400) with
| (_55_396, _55_398, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _145_319))
in (FStar_List.map (wl_prob_to_string wl) _145_320))
in (FStar_All.pipe_right _145_321 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let _55_419 = (match ((let _145_328 = (FStar_Syntax_Subst.compress k)
in _145_328.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if ((FStar_List.length bs) = (FStar_List.length ys)) then begin
(let _145_329 = (FStar_Syntax_Subst.open_comp bs c)
in ((ys, t), _145_329))
end else begin
(

let _55_410 = (FStar_Syntax_Util.abs_formals t)
in (match (_55_410) with
| (ys', t) -> begin
(let _145_330 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((FStar_List.append ys ys'), t), _145_330))
end))
end
end
| _55_412 -> begin
(let _145_332 = (let _145_331 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _145_331))
in ((ys, t), _145_332))
end)
in (match (_55_419) with
| ((ys, t), (xs, c)) -> begin
if ((FStar_List.length xs) <> (FStar_List.length ys)) then begin
(FStar_Syntax_Util.abs ys t (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))
end else begin
(

let c = (let _145_333 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp _145_333 c))
in (let _145_337 = (let _145_336 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _145_334 -> FStar_Util.Inl (_145_334)))
in (FStar_All.pipe_right _145_336 (fun _145_335 -> Some (_145_335))))
in (FStar_Syntax_Util.abs ys t _145_337)))
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

let _55_433 = (p_guard prob)
in (match (_55_433) with
| (_55_431, uv) -> begin
(

let _55_444 = (match ((let _145_348 = (FStar_Syntax_Subst.compress uv)
in _145_348.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi = (u_abs k bs phi)
in (

let _55_440 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _145_351 = (FStar_Util.string_of_int (p_pid prob))
in (let _145_350 = (FStar_Syntax_Print.term_to_string uv)
in (let _145_349 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _145_351 _145_350 _145_349))))
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi))))
end
| _55_443 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (

let _55_446 = (commit uvis)
in (

let _55_448 = wl
in {attempting = _55_448.attempting; wl_deferred = _55_448.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _55_448.defer_ok; smt_ok = _55_448.smt_ok; tcenv = _55_448.tcenv})))
end))))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> (

let _55_453 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_360 = (FStar_Util.string_of_int pid)
in (let _145_359 = (let _145_358 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _145_358 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _145_360 _145_359)))
end else begin
()
end
in (

let _55_455 = (commit sol)
in (

let _55_457 = wl
in {attempting = _55_457.attempting; wl_deferred = _55_457.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _55_457.defer_ok; smt_ok = _55_457.smt_ok; tcenv = _55_457.tcenv}))))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (

let conj_guard = (fun t g -> (match ((t, g)) with
| (_55_467, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(let _145_373 = (FStar_Syntax_Util.mk_conj t f)
in Some (_145_373))
end))
in (

let _55_479 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_376 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _145_375 = (let _145_374 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _145_374 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _145_376 _145_375)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))


let rec occurs = (fun wl uk t -> (let _145_386 = (let _145_384 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _145_384 FStar_Util.set_elements))
in (FStar_All.pipe_right _145_386 (FStar_Util.for_some (fun _55_488 -> (match (_55_488) with
| (uv, _55_487) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))


let occurs_check = (fun env wl uk t -> (

let occurs_ok = (not ((occurs wl uk t)))
in (

let msg = if occurs_ok then begin
None
end else begin
(let _145_393 = (let _145_392 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _145_391 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _145_392 _145_391)))
in Some (_145_393))
end
in (occurs_ok, msg))))


let occurs_and_freevars_check = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let _55_503 = (occurs_check env wl uk t)
in (match (_55_503) with
| (occurs_ok, msg) -> begin
(let _145_399 = (FStar_Util.set_is_subset_of fvs_t fvs)
in (occurs_ok, _145_399, (msg, fvs, fvs_t)))
end))))


let intersect_vars = (fun v1 v2 -> (

let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set v1)
in (

let _55_521 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _55_513 _55_516 -> (match ((_55_513, _55_516)) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _145_408 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _145_408)) then begin
(isect, isect_set)
end else begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _145_409 = (FStar_Util.set_add x isect_set)
in (((x, imp))::isect, _145_409))
end else begin
(isect, isect_set)
end)
end
end)) ([], FStar_Syntax_Syntax.no_names)))
in (match (_55_521) with
| (isect, _55_520) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _55_527 _55_531 -> (match ((_55_527, _55_531)) with
| ((a, _55_526), (b, _55_530)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt = (fun env seen arg -> (

let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _55_541 -> (match (_55_541) with
| (b, _55_540) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some ((a, (Prims.snd hd)))
end
end
| _55_543 -> begin
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

let _55_552 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_424 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _145_424))
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
(t, uv, k, [])
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _55_566; FStar_Syntax_Syntax.pos = _55_564; FStar_Syntax_Syntax.vars = _55_562}, args) -> begin
(t, uv, k, args)
end
| _55_576 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))


let destruct_flex_pattern = (fun env t -> (

let _55_583 = (destruct_flex_t t)
in (match (_55_583) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _55_587 -> begin
((t, uv, k, args), None)
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
| MisMatch (_55_590) -> begin
_55_590
end))


let head_match : match_result  ->  match_result = (fun _55_18 -> (match (_55_18) with
| MisMatch (i, j) -> begin
MisMatch ((i, j))
end
| _55_597 -> begin
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
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_name (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
if (FStar_Syntax_Syntax.bv_eq x y) then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
if (FStar_Syntax_Syntax.fv_eq f g) then begin
FullMatch
end else begin
MisMatch ((Some ((fv_delta_depth env f)), Some ((fv_delta_depth env g))))
end
end
| (FStar_Syntax_Syntax.Tm_uinst (f, _55_683), FStar_Syntax_Syntax.Tm_uinst (g, _55_688)) -> begin
(let _145_460 = (head_matches env f g)
in (FStar_All.pipe_right _145_460 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _55_699), FStar_Syntax_Syntax.Tm_uvar (uv', _55_704)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_710), FStar_Syntax_Syntax.Tm_refine (y, _55_715)) -> begin
(let _145_461 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _145_461 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_721), _55_725) -> begin
(let _145_462 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _145_462 head_match))
end
| (_55_728, FStar_Syntax_Syntax.Tm_refine (x, _55_731)) -> begin
(let _145_463 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _145_463 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _55_751), FStar_Syntax_Syntax.Tm_app (head', _55_756)) -> begin
(let _145_464 = (head_matches env head head')
in (FStar_All.pipe_right _145_464 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head, _55_762), _55_766) -> begin
(let _145_465 = (head_matches env head t2)
in (FStar_All.pipe_right _145_465 head_match))
end
| (_55_769, FStar_Syntax_Syntax.Tm_app (head, _55_772)) -> begin
(let _145_466 = (head_matches env t1 head)
in (FStar_All.pipe_right _145_466 head_match))
end
| _55_777 -> begin
(let _145_469 = (let _145_468 = (delta_depth_of_term env t1)
in (let _145_467 = (delta_depth_of_term env t2)
in (_145_468, _145_467)))
in MisMatch (_145_469))
end))))


let head_matches_delta = (fun env wl t1 t2 -> (

let success = (fun d r t1 t2 -> (r, if (d > 0) then begin
Some ((t1, t2))
end else begin
None
end))
in (

let fail = (fun r -> (r, None))
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

let _55_828 = if d1_greater_than_d2 then begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (t1', t2))
end else begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (let _145_490 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (t1, _145_490)))
end
in (match (_55_828) with
| (t1, t2) -> begin
(aux (n_delta + 1) t1 t2)
end)))
end
| MisMatch (_55_830) -> begin
(fail r)
end
| _55_833 -> begin
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
| T (_55_836) -> begin
_55_836
end))


let ___C____0 = (fun projectee -> (match (projectee) with
| C (_55_839) -> begin
_55_839
end))


type tcs =
tc Prims.list


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (match ((head_matches env t t')) with
| MisMatch (_55_846) -> begin
false
end
| _55_849 -> begin
true
end))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(

let rebuild = (fun args' -> (

let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((_55_859, imp), T (t)) -> begin
(t, imp)
end
| _55_866 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((hd, args))) None t.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _55_871 -> (match (_55_871) with
| (t, _55_870) -> begin
(None, INVARIANT, T (t))
end))))
in (rebuild, matches, tcs)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let fail = (fun _55_878 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (

let _55_881 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_55_881) with
| (bs, c) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs tcs -> (match ((bs, tcs)) with
| (((x, imp))::bs, (T (t))::tcs) -> begin
(aux ((((

let _55_898 = x
in {FStar_Syntax_Syntax.ppname = _55_898.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_898.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp))::out) bs tcs)
end
| ([], (C (c))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _55_906 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (

let rec decompose = (fun out _55_19 -> (match (_55_19) with
| [] -> begin
(FStar_List.rev (((None, COVARIANT, C (c)))::out))
end
| (hd)::rest -> begin
(decompose (((Some (hd), CONTRAVARIANT, T ((Prims.fst hd).FStar_Syntax_Syntax.sort)))::out) rest)
end))
in (let _145_572 = (decompose [] bs)
in (rebuild, matches, _145_572))))
end)))
end
| _55_915 -> begin
(

let rebuild = (fun _55_20 -> (match (_55_20) with
| [] -> begin
t
end
| _55_919 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _55_21 -> (match (_55_21) with
| T (t) -> begin
t
end
| _55_926 -> begin
(FStar_All.failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _55_22 -> (match (_55_22) with
| T (t) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _55_931 -> begin
(FStar_All.failwith "Impossible")
end))


let imitation_sub_probs = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope args q -> (match (q) with
| (_55_944, variance, T (ti)) -> begin
(

let k = (

let _55_952 = (FStar_Syntax_Util.type_u ())
in (match (_55_952) with
| (t, _55_951) -> begin
(let _145_594 = (new_uvar r scope t)
in (Prims.fst _145_594))
end))
in (

let _55_956 = (new_uvar r scope k)
in (match (_55_956) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| _55_959 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((gi, args))) None r)
end)
in (let _145_597 = (let _145_596 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _145_595 -> FStar_TypeChecker_Common.TProb (_145_595)) _145_596))
in (T (gi_xs), _145_597)))
end)))
end
| (_55_962, _55_964, C (_55_966)) -> begin
(FStar_All.failwith "impos")
end))
in (

let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
([], [], FStar_Syntax_Util.t_true)
end
| (q)::qs -> begin
(

let _55_1044 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti); FStar_Syntax_Syntax.tk = _55_984; FStar_Syntax_Syntax.pos = _55_982; FStar_Syntax_Syntax.vars = _55_980})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _145_606 = (let _145_605 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _145_604 -> C (_145_604)) _145_605))
in (_145_606, (prob)::[]))
end
| _55_995 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti); FStar_Syntax_Syntax.tk = _55_1003; FStar_Syntax_Syntax.pos = _55_1001; FStar_Syntax_Syntax.vars = _55_999})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _145_609 = (let _145_608 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _145_607 -> C (_145_607)) _145_608))
in (_145_609, (prob)::[]))
end
| _55_1014 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_55_1016, _55_1018, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _55_1024; FStar_Syntax_Syntax.pos = _55_1022; FStar_Syntax_Syntax.vars = _55_1020})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> (None, INVARIANT, T ((Prims.fst t))))))
in (

let components = ((None, COVARIANT, T (c.FStar_Syntax_Syntax.result_typ)))::components
in (

let _55_1035 = (let _145_611 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _145_611 FStar_List.unzip))
in (match (_55_1035) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (let _145_616 = (let _145_615 = (let _145_612 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _145_612 un_T))
in (let _145_614 = (let _145_613 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _145_613 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _145_615; FStar_Syntax_Syntax.effect_args = _145_614; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _145_616))
in (C (gi_xs), sub_probs))
end))))
end
| _55_1038 -> begin
(

let _55_1041 = (sub_prob scope args q)
in (match (_55_1041) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_55_1044) with
| (tc, probs) -> begin
(

let _55_1057 = (match (q) with
| (Some (b), _55_1048, _55_1050) -> begin
(let _145_618 = (let _145_617 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_145_617)::args)
in (Some (b), (b)::scope, _145_618))
end
| _55_1053 -> begin
(None, scope, args)
end)
in (match (_55_1057) with
| (bopt, scope, args) -> begin
(

let _55_1061 = (aux scope args qs)
in (match (_55_1061) with
| (sub_probs, tcs, f) -> begin
(

let f = (match (bopt) with
| None -> begin
(let _145_621 = (let _145_620 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_145_620)
in (FStar_Syntax_Util.mk_conj_l _145_621))
end
| Some (b) -> begin
(let _145_625 = (let _145_624 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _145_623 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_145_624)::_145_623))
in (FStar_Syntax_Util.mk_conj_l _145_625))
end)
in ((FStar_List.append probs sub_probs), (tc)::tcs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))


let rec eq_tm : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t1 t2 -> (

let t1 = (FStar_Syntax_Subst.compress t1)
in (

let t2 = (FStar_Syntax_Subst.compress t2)
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(FStar_Syntax_Syntax.fv_eq f g)
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(c = d)
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, _55_1089), FStar_Syntax_Syntax.Tm_uvar (u2, _55_1094)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _55_1108 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _55_1114 _55_1118 -> (match ((_55_1114, _55_1118)) with
| ((a1, _55_1113), (a2, _55_1117)) -> begin
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

let _55_1121 = p
in (let _145_647 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _145_646 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _55_1121.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _145_647; FStar_TypeChecker_Common.relation = _55_1121.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _145_646; FStar_TypeChecker_Common.element = _55_1121.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1121.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1121.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1121.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1121.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1121.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _145_653 = (compress_tprob wl p)
in (FStar_All.pipe_right _145_653 (fun _145_652 -> FStar_TypeChecker_Common.TProb (_145_652))))
end
| FStar_TypeChecker_Common.CProb (_55_1128) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (let _145_658 = (compress_prob wl pr)
in (FStar_All.pipe_right _145_658 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let _55_1138 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1138) with
| (lh, _55_1137) -> begin
(

let _55_1142 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1142) with
| (rh, _55_1141) -> begin
(

let _55_1198 = (match ((lh.FStar_Syntax_Syntax.n, rh.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_55_1144), FStar_Syntax_Syntax.Tm_uvar (_55_1147)) -> begin
(flex_flex, tp)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Syntax_Syntax.Tm_uvar (_55_1163), _55_1166) -> begin
(

let _55_1170 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1170) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _55_1173 -> begin
(

let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _145_660 = (

let _55_1175 = tp
in (let _145_659 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _55_1175.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1175.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1175.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _145_659; FStar_TypeChecker_Common.element = _55_1175.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1175.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1175.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1175.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1175.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1175.FStar_TypeChecker_Common.rank}))
in (rank, _145_660)))
end)
end))
end
| (_55_1178, FStar_Syntax_Syntax.Tm_uvar (_55_1180)) -> begin
(

let _55_1185 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1185) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _55_1188 -> begin
(let _145_662 = (

let _55_1189 = tp
in (let _145_661 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _55_1189.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _145_661; FStar_TypeChecker_Common.relation = _55_1189.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1189.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1189.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1189.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1189.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1189.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1189.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1189.FStar_TypeChecker_Common.rank}))
in (refine_flex, _145_662))
end)
end))
end
| (_55_1192, _55_1194) -> begin
(rigid_rigid, tp)
end)
in (match (_55_1198) with
| (rank, tp) -> begin
(let _145_664 = (FStar_All.pipe_right (

let _55_1199 = tp
in {FStar_TypeChecker_Common.pid = _55_1199.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1199.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1199.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1199.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1199.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1199.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1199.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1199.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1199.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _145_663 -> FStar_TypeChecker_Common.TProb (_145_663)))
in (rank, _145_664))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _145_666 = (FStar_All.pipe_right (

let _55_1203 = cp
in {FStar_TypeChecker_Common.pid = _55_1203.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1203.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1203.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1203.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1203.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1203.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1203.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1203.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1203.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _145_665 -> FStar_TypeChecker_Common.CProb (_145_665)))
in (rigid_rigid, _145_666))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun _55_1210 probs -> (match (_55_1210) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| (hd)::tl -> begin
(

let _55_1218 = (rank wl hd)
in (match (_55_1218) with
| (rank, hd) -> begin
if (rank <= flex_rigid_eq) then begin
(match (min) with
| None -> begin
(Some (hd), (FStar_List.append out tl), rank)
end
| Some (m) -> begin
(Some (hd), (FStar_List.append out ((m)::tl)), rank)
end)
end else begin
if (rank < min_rank) then begin
(match (min) with
| None -> begin
(aux (rank, Some (hd), out) tl)
end
| Some (m) -> begin
(aux (rank, Some (hd), (m)::out) tl)
end)
end else begin
(aux (min_rank, min, (hd)::out) tl)
end
end
end))
end)
end))
in (aux ((flex_flex + 1), None, []) wl.attempting)))


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
| UDeferred (_55_1229) -> begin
_55_1229
end))


let ___USolved____0 = (fun projectee -> (match (projectee) with
| USolved (_55_1232) -> begin
_55_1232
end))


let ___UFailed____0 = (fun projectee -> (match (projectee) with
| UFailed (_55_1235) -> begin
_55_1235
end))


let rec solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (

let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (

let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (

let _55_1251 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_1251) with
| (k, _55_1250) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _55_1255 -> begin
false
end)
end)))))
end
| _55_1257 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (

let try_umax_components = (fun u1 u2 msg -> (match ((u1, u2)) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
if ((FStar_List.length us1) = (FStar_List.length us2)) then begin
(

let rec aux = (fun wl us1 us2 -> (match ((us1, us2)) with
| ((u1)::us1, (u2)::us2) -> begin
(match ((solve_universe_eq orig wl u1 u2)) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed -> begin
failed
end)
end
| _55_1282 -> begin
USolved (wl)
end))
in (aux wl us1 us2))
end else begin
(let _145_746 = (let _145_745 = (FStar_Syntax_Print.univ_to_string u1)
in (let _145_744 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _145_745 _145_744)))
in UFailed (_145_746))
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
| _55_1300 -> begin
(let _145_753 = (let _145_752 = (FStar_Syntax_Print.univ_to_string u1)
in (let _145_751 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _145_752 _145_751 msg)))
in UFailed (_145_753))
end))
in (match ((u1, u2)) with
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

let wl = (extend_solution orig ((UNIV ((v1, u2)))::[]) wl)
in USolved (wl))
end
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(

let u = (norm_univ wl u)
in if (occurs_univ v1 u) then begin
(let _145_756 = (let _145_755 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _145_754 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _145_755 _145_754)))
in (try_umax_components u1 u2 _145_756))
end else begin
(let _145_757 = (extend_solution orig ((UNIV ((v1, u)))::[]) wl)
in USolved (_145_757))
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

let _55_1397 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_803 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _145_803))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(

let probs = (

let _55_1404 = probs
in {attempting = tl; wl_deferred = _55_1404.wl_deferred; ctr = _55_1404.ctr; defer_ok = _55_1404.defer_ok; smt_ok = _55_1404.smt_ok; tcenv = _55_1404.tcenv})
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
| (None, _55_1419, _55_1421) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _55_1425 -> begin
(

let _55_1434 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _55_1431 -> (match (_55_1431) with
| (c, _55_1428, _55_1430) -> begin
(c < probs.ctr)
end))))
in (match (_55_1434) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _145_806 = (FStar_List.map (fun _55_1440 -> (match (_55_1440) with
| (_55_1437, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in Success (_145_806))
end
| _55_1442 -> begin
(let _145_809 = (

let _55_1443 = probs
in (let _145_808 = (FStar_All.pipe_right attempt (FStar_List.map (fun _55_1450 -> (match (_55_1450) with
| (_55_1446, _55_1448, y) -> begin
y
end))))
in {attempting = _145_808; wl_deferred = rest; ctr = _55_1443.ctr; defer_ok = _55_1443.defer_ok; smt_ok = _55_1443.smt_ok; tcenv = _55_1443.tcenv}))
in (solve env _145_809))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _145_815 = (solve_prob orig None [] wl)
in (solve env _145_815))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (

let rec aux = (fun wl us1 us2 -> (match ((us1, us2)) with
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
| _55_1485 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t1 = (whnf env t1)
in (

let t2 = (whnf env t2)
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _55_1493; FStar_Syntax_Syntax.pos = _55_1491; FStar_Syntax_Syntax.vars = _55_1489}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _55_1505; FStar_Syntax_Syntax.pos = _55_1503; FStar_Syntax_Syntax.vars = _55_1501}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (

let _55_1514 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _55_1529 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(

let _55_1534 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_831 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _145_831 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (

let _55_1539 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_835 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" _145_835))
end else begin
()
end
in (

let _55_1543 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1543) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let _55_1549 = (head_matches_delta env () t1 t2)
in (match (_55_1549) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (_55_1551) -> begin
None
end
| FullMatch -> begin
(match (ts) with
| None -> begin
Some ((t1, []))
end
| Some (t1, t2) -> begin
Some ((t1, []))
end)
end
| HeadMatch -> begin
(

let _55_1567 = (match (ts) with
| Some (t1, t2) -> begin
(let _145_841 = (FStar_Syntax_Subst.compress t1)
in (let _145_840 = (FStar_Syntax_Subst.compress t2)
in (_145_841, _145_840)))
end
| None -> begin
(let _145_843 = (FStar_Syntax_Subst.compress t1)
in (let _145_842 = (FStar_Syntax_Subst.compress t2)
in (_145_843, _145_842)))
end)
in (match (_55_1567) with
| (t1, t2) -> begin
(

let eq_prob = (fun t1 t2 -> (let _145_849 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _145_848 -> FStar_TypeChecker_Common.TProb (_145_848)) _145_849)))
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(let _145_856 = (let _145_855 = (let _145_852 = (let _145_851 = (let _145_850 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in (x, _145_850))
in FStar_Syntax_Syntax.Tm_refine (_145_851))
in (FStar_Syntax_Syntax.mk _145_852 None t1.FStar_Syntax_Syntax.pos))
in (let _145_854 = (let _145_853 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (_145_853)::[])
in (_145_855, _145_854)))
in Some (_145_856))
end
| (_55_1581, FStar_Syntax_Syntax.Tm_refine (x, _55_1584)) -> begin
(let _145_859 = (let _145_858 = (let _145_857 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (_145_857)::[])
in (t1, _145_858))
in Some (_145_859))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_1590), _55_1594) -> begin
(let _145_862 = (let _145_861 = (let _145_860 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (_145_860)::[])
in (t2, _145_861))
in Some (_145_862))
end
| _55_1597 -> begin
(

let _55_1601 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1601) with
| (head1, _55_1600) -> begin
(match ((let _145_863 = (FStar_Syntax_Util.un_uinst head1)
in _145_863.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _55_1607; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_unfoldable (i); FStar_Syntax_Syntax.fv_qual = _55_1603}) -> begin
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
| _55_1614 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, _55_1618) -> begin
(

let _55_1643 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _55_23 -> (match (_55_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(

let _55_1629 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1629) with
| (u', _55_1628) -> begin
(match ((let _145_865 = (whnf env u')
in _145_865.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _55_1632) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _55_1636 -> begin
false
end)
end))
end
| _55_1638 -> begin
false
end)
end
| _55_1640 -> begin
false
end))))
in (match (_55_1643) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun _55_1647 tps -> (match (_55_1647) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(match ((let _145_870 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound _145_870))) with
| Some (bound, sub) -> begin
(make_lower_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _55_1660 -> begin
None
end)
end))
in (match ((let _145_872 = (let _145_871 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in (_145_871, []))
in (make_lower_bound _145_872 lower_bounds))) with
| None -> begin
(

let _55_1662 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
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

let _55_1672 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(

let wl' = (

let _55_1669 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _55_1669.wl_deferred; ctr = _55_1669.ctr; defer_ok = _55_1669.defer_ok; smt_ok = _55_1669.smt_ok; tcenv = _55_1669.tcenv})
in (let _145_873 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" _145_873)))
end else begin
()
end
in (match ((solve_t env eq_prob (

let _55_1674 = wl
in {attempting = sub_probs; wl_deferred = _55_1674.wl_deferred; ctr = _55_1674.ctr; defer_ok = _55_1674.defer_ok; smt_ok = _55_1674.smt_ok; tcenv = _55_1674.tcenv}))) with
| Success (_55_1677) -> begin
(

let wl = (

let _55_1679 = wl
in {attempting = rest; wl_deferred = _55_1679.wl_deferred; ctr = _55_1679.ctr; defer_ok = _55_1679.defer_ok; smt_ok = _55_1679.smt_ok; tcenv = _55_1679.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let _55_1685 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| _55_1688 -> begin
None
end)))
end))
end))
end
| _55_1690 -> begin
(FStar_All.failwith "Impossible: Not a rigid-flex")
end)))
end))))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (

let _55_1694 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_879 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _145_879))
end else begin
()
end
in (

let _55_1698 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1698) with
| (u, args) -> begin
(

let _55_1704 = (0, 1, 2, 3, 4)
in (match (_55_1704) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(

let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (

let base_types_match = (fun t1 t2 -> (

let _55_1713 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1713) with
| (h1, args1) -> begin
(

let _55_1717 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_1717) with
| (h2, _55_1716) -> begin
(match ((h1.FStar_Syntax_Syntax.n, h2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _145_891 = (let _145_890 = (let _145_889 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _145_888 -> FStar_TypeChecker_Common.TProb (_145_888)) _145_889))
in (_145_890)::[])
in Some (_145_891))
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
(let _145_895 = (let _145_894 = (let _145_893 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _145_892 -> FStar_TypeChecker_Common.TProb (_145_892)) _145_893))
in (_145_894)::[])
in Some (_145_895))
end
end else begin
None
end
end
| _55_1729 -> begin
None
end)
end))
end)))
in (

let conjoin = (fun t1 t2 -> (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
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

let subst = (FStar_Syntax_Syntax.DB ((0, x)))::[]
in (

let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (

let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let _145_902 = (let _145_901 = (let _145_900 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _145_900))
in (_145_901, m))
in Some (_145_902))))))
end))
end
| (_55_1751, FStar_Syntax_Syntax.Tm_refine (y, _55_1754)) -> begin
(

let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_1764), _55_1768) -> begin
(

let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _55_1775 -> begin
(

let m = (base_types_match t1 t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end))
in (

let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _55_1783) -> begin
(

let _55_1808 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _55_24 -> (match (_55_24) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(

let _55_1794 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1794) with
| (u', _55_1793) -> begin
(match ((let _145_904 = (whnf env u')
in _145_904.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _55_1797) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _55_1801 -> begin
false
end)
end))
end
| _55_1803 -> begin
false
end)
end
| _55_1805 -> begin
false
end))))
in (match (_55_1808) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun _55_1812 tps -> (match (_55_1812) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(match ((let _145_909 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _145_909))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _55_1825 -> begin
None
end)
end))
in (match ((let _145_911 = (let _145_910 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in (_145_910, []))
in (make_upper_bound _145_911 upper_bounds))) with
| None -> begin
(

let _55_1827 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
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

let _55_1837 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(

let wl' = (

let _55_1834 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _55_1834.wl_deferred; ctr = _55_1834.ctr; defer_ok = _55_1834.defer_ok; smt_ok = _55_1834.smt_ok; tcenv = _55_1834.tcenv})
in (let _145_912 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _145_912)))
end else begin
()
end
in (match ((solve_t env eq_prob (

let _55_1839 = wl
in {attempting = sub_probs; wl_deferred = _55_1839.wl_deferred; ctr = _55_1839.ctr; defer_ok = _55_1839.defer_ok; smt_ok = _55_1839.smt_ok; tcenv = _55_1839.tcenv}))) with
| Success (_55_1842) -> begin
(

let wl = (

let _55_1844 = wl
in {attempting = rest; wl_deferred = _55_1844.wl_deferred; ctr = _55_1844.ctr; defer_ok = _55_1844.defer_ok; smt_ok = _55_1844.smt_ok; tcenv = _55_1844.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let _55_1850 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _55_1853 -> begin
None
end)))
end))
end))
end
| _55_1855 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (

let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(

let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (

let _55_1872 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_940 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _145_940))
end else begin
()
end
in (

let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula)))))
end
| (((hd1, imp))::xs, ((hd2, imp'))::ys) when (imp = imp') -> begin
(

let hd1 = (

let _55_1886 = hd1
in (let _145_941 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1886.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1886.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_941}))
in (

let hd2 = (

let _55_1889 = hd2
in (let _145_942 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1889.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1889.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_942}))
in (

let prob = (let _145_945 = (let _145_944 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _145_944 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _145_943 -> FStar_TypeChecker_Common.TProb (_145_943)) _145_945))
in (

let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (

let subst = (let _145_946 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (FStar_Syntax_Syntax.DB ((0, hd1)))::_145_946)
in (

let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux (((hd1, imp))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi = (let _145_948 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _145_947 = (FStar_Syntax_Util.close_forall (((hd1, imp))::[]) phi)
in (FStar_Syntax_Util.mk_conj _145_948 _145_947)))
in (

let _55_1901 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_950 = (FStar_Syntax_Print.term_to_string phi)
in (let _145_949 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _145_950 _145_949)))
end else begin
()
end
in FStar_Util.Inl (((prob)::sub_probs, phi))))
end
| fail -> begin
fail
end)))))))
end
| _55_1905 -> begin
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
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _145_954 = (compress_tprob wl problem)
in (solve_t' env _145_954 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (

let _55_1933 = (head_matches_delta env wl t1 t2)
in (match (_55_1933) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch (_55_1935), _55_1938) -> begin
(

let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _55_1951 -> begin
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
in (let _145_983 = (let _145_982 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _145_982 t2))
in (FStar_Syntax_Util.mk_forall x _145_983)))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
in (let _145_984 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _145_984)))
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_55_1961, Some (t1, t2)) -> begin
(solve_t env (

let _55_1967 = problem
in {FStar_TypeChecker_Common.pid = _55_1967.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_1967.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_1967.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1967.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1967.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1967.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1967.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1967.FStar_TypeChecker_Common.rank}) wl)
end
| (_55_1970, None) -> begin
(

let _55_1973 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_988 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_987 = (FStar_Syntax_Print.tag_of_term t1)
in (let _145_986 = (FStar_Syntax_Print.term_to_string t2)
in (let _145_985 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _145_988 _145_987 _145_986 _145_985)))))
end else begin
()
end
in (

let _55_1977 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1977) with
| (head1, args1) -> begin
(

let _55_1980 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_1980) with
| (head2, args2) -> begin
(

let nargs = (FStar_List.length args1)
in if (nargs <> (FStar_List.length args2)) then begin
(let _145_993 = (let _145_992 = (FStar_Syntax_Print.term_to_string head1)
in (let _145_991 = (args_to_string args1)
in (let _145_990 = (FStar_Syntax_Print.term_to_string head2)
in (let _145_989 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _145_992 _145_991 _145_990 _145_989)))))
in (giveup env _145_993 orig))
end else begin
if ((nargs = 0) || (eq_args args1 args2)) then begin
(match ((solve_maybe_uinsts env orig head1 head2 wl)) with
| USolved (wl) -> begin
(let _145_994 = (solve_prob orig None [] wl)
in (solve env _145_994))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(

let _55_1990 = (base_and_refinement env wl t1)
in (match (_55_1990) with
| (base1, refinement1) -> begin
(

let _55_1993 = (base_and_refinement env wl t2)
in (match (_55_1993) with
| (base2, refinement2) -> begin
(match ((refinement1, refinement2)) with
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

let subprobs = (FStar_List.map2 (fun _55_2006 _55_2010 -> (match ((_55_2006, _55_2010)) with
| ((a, _55_2005), (a', _55_2009)) -> begin
(let _145_998 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _145_997 -> FStar_TypeChecker_Common.TProb (_145_997)) _145_998))
end)) args1 args2)
in (

let formula = (let _145_1000 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _145_1000))
in (

let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _55_2016 -> begin
(

let lhs = (force_refinement (base1, refinement1))
in (

let rhs = (force_refinement (base2, refinement2))
in (solve_t env (

let _55_2019 = problem
in {FStar_TypeChecker_Common.pid = _55_2019.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _55_2019.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _55_2019.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2019.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2019.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2019.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2019.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2019.FStar_TypeChecker_Common.rank}) wl)))
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

let _55_2038 = p
in (match (_55_2038) with
| (((u, k), xs, c), ps, (h, _55_2035, qs)) -> begin
(

let xs = (sn_binders env xs)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _55_2044 = (imitation_sub_probs orig env xs ps qs)
in (match (_55_2044) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (let _145_1015 = (h gs_xs)
in (let _145_1014 = (let _145_1013 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _145_1011 -> FStar_Util.Inl (_145_1011)))
in (FStar_All.pipe_right _145_1013 (fun _145_1012 -> Some (_145_1012))))
in (FStar_Syntax_Util.abs xs _145_1015 _145_1014)))
in (

let _55_2046 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1022 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _145_1021 = (FStar_Syntax_Print.comp_to_string c)
in (let _145_1020 = (FStar_Syntax_Print.term_to_string im)
in (let _145_1019 = (FStar_Syntax_Print.tag_of_term im)
in (let _145_1018 = (let _145_1016 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _145_1016 (FStar_String.concat ", ")))
in (let _145_1017 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are %s, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" _145_1022 _145_1021 _145_1020 _145_1019 _145_1018 _145_1017)))))))
end else begin
()
end
in (

let wl = (solve_prob orig (Some (formula)) ((TERM (((u, k), im)))::[]) wl)
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

let _55_2072 = p
in (match (_55_2072) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _55_2077 = (FStar_List.nth ps i)
in (match (_55_2077) with
| (pi, _55_2076) -> begin
(

let _55_2081 = (FStar_List.nth xs i)
in (match (_55_2081) with
| (xi, _55_2080) -> begin
(

let rec gs = (fun k -> (

let _55_2086 = (FStar_Syntax_Util.arrow_formals k)
in (match (_55_2086) with
| (bs, k) -> begin
(

let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| ((a, _55_2094))::tl -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (

let _55_2100 = (new_uvar r xs k_a)
in (match (_55_2100) with
| (gi_xs, gi) -> begin
(

let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (

let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst = (FStar_Syntax_Syntax.NT ((a, gi_xs)))::subst
in (

let _55_2106 = (aux subst tl)
in (match (_55_2106) with
| (gi_xs', gi_ps') -> begin
(let _145_1052 = (let _145_1049 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_145_1049)::gi_xs')
in (let _145_1051 = (let _145_1050 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_145_1050)::gi_ps')
in (_145_1052, _145_1051)))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _145_1053 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _145_1053)) then begin
None
end else begin
(

let _55_2110 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_55_2110) with
| (g_xs, _55_2109) -> begin
(

let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (let _145_1058 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (let _145_1057 = (let _145_1056 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _145_1054 -> FStar_Util.Inl (_145_1054)))
in (FStar_All.pipe_right _145_1056 (fun _145_1055 -> Some (_145_1055))))
in (FStar_Syntax_Util.abs xs _145_1058 _145_1057)))
in (

let sub = (let _145_1064 = (let _145_1063 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _145_1062 = (let _145_1061 = (FStar_List.map (fun _55_2118 -> (match (_55_2118) with
| (_55_2114, _55_2116, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _145_1061))
in (mk_problem (p_scope orig) orig _145_1063 (p_rel orig) _145_1062 None "projection")))
in (FStar_All.pipe_left (fun _145_1059 -> FStar_TypeChecker_Common.TProb (_145_1059)) _145_1064))
in (

let _55_2120 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1066 = (FStar_Syntax_Print.term_to_string proj)
in (let _145_1065 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _145_1066 _145_1065)))
end else begin
()
end
in (

let wl = (let _145_1068 = (let _145_1067 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_145_1067))
in (solve_prob orig _145_1068 ((TERM ((u, proj)))::[]) wl))
in (let _145_1070 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _145_1069 -> Some (_145_1069)) _145_1070)))))))
end))
end)
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun orig lhs t2 wl -> (

let _55_2134 = lhs
in (match (_55_2134) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let _55_2139 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (_55_2139) with
| (xs, c) -> begin
if ((FStar_List.length xs) = (FStar_List.length ps)) then begin
(let _145_1092 = (let _145_1091 = (decompose env t2)
in (((uv, k_uv), xs, c), ps, _145_1091))
in Some (_145_1092))
end else begin
(

let k_uv = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (match ((let _145_1098 = (let _145_1097 = (FStar_Syntax_Subst.compress k)
in _145_1097.FStar_Syntax_Syntax.n)
in (_145_1098, args))) with
| (_55_2145, []) -> begin
(let _145_1100 = (let _145_1099 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _145_1099))
in Some (_145_1100))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(

let _55_2162 = (FStar_Syntax_Util.head_and_args k)
in (match (_55_2162) with
| (uv, uv_args) -> begin
(match ((let _145_1101 = (FStar_Syntax_Subst.compress uv)
in _145_1101.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, _55_2165) -> begin
(match ((pat_vars env [] uv_args)) with
| None -> begin
None
end
| Some (scope) -> begin
(

let xs = (FStar_All.pipe_right args (FStar_List.map (fun _55_2171 -> (let _145_1107 = (let _145_1106 = (let _145_1105 = (let _145_1104 = (let _145_1103 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _145_1103 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _145_1104))
in (Prims.fst _145_1105))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) _145_1106))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _145_1107)))))
in (

let c = (let _145_1111 = (let _145_1110 = (let _145_1109 = (let _145_1108 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _145_1108 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _145_1109))
in (Prims.fst _145_1110))
in (FStar_Syntax_Syntax.mk_Total _145_1111))
in (

let k' = (FStar_Syntax_Util.arrow xs c)
in (

let uv_sol = (let _145_1117 = (let _145_1116 = (let _145_1115 = (let _145_1114 = (let _145_1113 = (let _145_1112 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _145_1112 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total _145_1113))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _145_1114))
in FStar_Util.Inl (_145_1115))
in Some (_145_1116))
in (FStar_Syntax_Util.abs scope k' _145_1117))
in (

let _55_2177 = (FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)))
in Some ((xs, c)))))))
end)
end
| _55_2180 -> begin
None
end)
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs, c), _55_2186) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs)
in if (n_xs = n_args) then begin
(let _145_1119 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right _145_1119 (fun _145_1118 -> Some (_145_1118))))
end else begin
if (n_xs < n_args) then begin
(

let _55_2192 = (FStar_Util.first_N n_xs args)
in (match (_55_2192) with
| (args, rest) -> begin
(

let _55_2195 = (FStar_Syntax_Subst.open_comp xs c)
in (match (_55_2195) with
| (xs, c) -> begin
(let _145_1121 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt _145_1121 (fun _55_2198 -> (match (_55_2198) with
| (xs', c) -> begin
Some (((FStar_List.append xs xs'), c))
end))))
end))
end))
end else begin
(

let _55_2201 = (FStar_Util.first_N n_args xs)
in (match (_55_2201) with
| (xs, rest) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) None k.FStar_Syntax_Syntax.pos)
in (let _145_1124 = (let _145_1122 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs _145_1122))
in (FStar_All.pipe_right _145_1124 (fun _145_1123 -> Some (_145_1123)))))
end))
end
end))
end
| _55_2204 -> begin
(let _145_1128 = (let _145_1127 = (FStar_Syntax_Print.uvar_to_string uv)
in (let _145_1126 = (FStar_Syntax_Print.term_to_string k)
in (let _145_1125 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" _145_1127 _145_1126 _145_1125))))
in (FStar_All.failwith _145_1128))
end))
in (let _145_1166 = (elim k_uv ps)
in (FStar_Util.bind_opt _145_1166 (fun _55_2207 -> (match (_55_2207) with
| (xs, c) -> begin
(let _145_1165 = (let _145_1164 = (decompose env t2)
in (((uv, k_uv), xs, c), ps, _145_1164))
in Some (_145_1165))
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
| Failed (_55_2215) -> begin
(

let _55_2217 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + 1)))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(

let _55_2225 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + 1)))
end
| Some (sol) -> begin
sol
end)
end))
end)
in (

let check_head = (fun fvs1 t2 -> (

let _55_2235 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_2235) with
| (hd, _55_2234) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _55_2246 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(

let _55_2248 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1177 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _145_1177))
end else begin
()
end
in false)
end)
end)
end)))
in (

let imitate_ok = (fun t2 -> (

let fvs_hd = (let _145_1181 = (let _145_1180 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _145_1180 Prims.fst))
in (FStar_All.pipe_right _145_1181 FStar_Syntax_Free.names))
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

let _55_2261 = (occurs_check env wl (uv, k_uv) t2)
in (match (_55_2261) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _145_1183 = (let _145_1182 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _145_1182))
in (giveup_or_defer orig _145_1183))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _145_1184 = (subterms args_lhs)
in (imitate' orig env wl _145_1184))
end else begin
(

let _55_2262 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1187 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_1186 = (names_to_string fvs1)
in (let _145_1185 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _145_1187 _145_1186 _145_1185))))
end else begin
()
end
in (

let sol = (match (vars) with
| [] -> begin
t2
end
| _55_2266 -> begin
(let _145_1188 = (sn_binders env vars)
in (u_abs k_uv _145_1188 t2))
end)
in (

let wl = (solve_prob orig None ((TERM (((uv, k_uv), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(

let _55_2269 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1191 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_1190 = (names_to_string fvs1)
in (let _145_1189 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _145_1191 _145_1190 _145_1189))))
end else begin
()
end
in (let _145_1192 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _145_1192 (- (1)))))
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
if (let _145_1193 = (FStar_Syntax_Free.names t1)
in (check_head _145_1193 t2)) then begin
(

let im_ok = (imitate_ok t2)
in (

let _55_2273 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1194 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _145_1194 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _145_1195 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _145_1195 im_ok))))
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

let force_quasi_pattern = (fun xs_opt _55_2285 -> (match (_55_2285) with
| (t, u, k, args) -> begin
(

let _55_2289 = (FStar_Syntax_Util.arrow_formals k)
in (match (_55_2289) with
| (all_formals, _55_2288) -> begin
(

let _55_2290 = ()
in (

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match ((formals, args)) with
| ([], []) -> begin
(

let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _55_2303 -> (match (_55_2303) with
| (x, imp) -> begin
(let _145_1217 = (FStar_Syntax_Syntax.bv_to_name x)
in (_145_1217, imp))
end))))
in (

let pattern_vars = (FStar_List.rev pattern_vars)
in (

let kk = (

let _55_2309 = (FStar_Syntax_Util.type_u ())
in (match (_55_2309) with
| (t, _55_2308) -> begin
(let _145_1218 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _145_1218))
end))
in (

let _55_2313 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_55_2313) with
| (t', tm_u1) -> begin
(

let _55_2320 = (destruct_flex_t t')
in (match (_55_2320) with
| (_55_2315, u1, k1, _55_2319) -> begin
(

let sol = (let _145_1220 = (let _145_1219 = (u_abs k all_formals t')
in ((u, k), _145_1219))
in TERM (_145_1220))
in (

let t_app = (FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args None t.FStar_Syntax_Syntax.pos)
in (sol, (t_app, u1, k1, pat_args))))
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _55_2339 -> (match (_55_2339) with
| (x, _55_2338) -> begin
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
(let _145_1222 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _145_1222 formals tl))
end)
end)
end)
end
| _55_2343 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _145_1223 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _145_1223 all_formals args))))
end))
end))
in (

let solve_both_pats = (fun wl _55_2350 _55_2355 r -> (match ((_55_2350, _55_2355)) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _145_1232 = (solve_prob orig None [] wl)
in (solve env _145_1232))
end else begin
(

let xs = (sn_binders env xs)
in (

let ys = (sn_binders env ys)
in (

let zs = (intersect_vars xs ys)
in (

let _55_2360 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1237 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _145_1236 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _145_1235 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (let _145_1234 = (FStar_Syntax_Print.term_to_string k1)
in (let _145_1233 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" _145_1237 _145_1236 _145_1235 _145_1234 _145_1233))))))
end else begin
()
end
in (

let _55_2373 = (

let _55_2365 = (FStar_Syntax_Util.type_u ())
in (match (_55_2365) with
| (t, _55_2364) -> begin
(

let _55_2369 = (new_uvar r zs t)
in (match (_55_2369) with
| (k, _55_2368) -> begin
(let _145_1243 = (let _145_1238 = (new_uvar r zs k)
in (FStar_All.pipe_left Prims.fst _145_1238))
in (let _145_1242 = (let _145_1239 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow xs _145_1239))
in (let _145_1241 = (let _145_1240 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow ys _145_1240))
in (_145_1243, _145_1242, _145_1241))))
end))
end))
in (match (_55_2373) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs u_zs)
in (

let _55_2377 = (occurs_check env wl (u1, k1) sub1)
in (match (_55_2377) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(

let sol1 = TERM (((u1, k1), sub1))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(

let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(

let sub2 = (u_abs knew2 ys u_zs)
in (

let _55_2383 = (occurs_check env wl (u2, k2) sub2)
in (match (_55_2383) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(

let sol2 = TERM (((u2, k2), sub2))
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

let solve_one_pat = (fun _55_2391 _55_2396 -> (match ((_55_2391, _55_2396)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(

let _55_2397 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1249 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_1248 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _145_1249 _145_1248)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(

let sub_probs = (FStar_List.map2 (fun _55_2402 _55_2406 -> (match ((_55_2402, _55_2406)) with
| ((a, _55_2401), (t2, _55_2405)) -> begin
(let _145_1254 = (let _145_1252 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _145_1252 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _145_1254 (fun _145_1253 -> FStar_TypeChecker_Common.TProb (_145_1253))))
end)) xs args2)
in (

let guard = (let _145_1256 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _145_1256))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(

let t2 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t2)
in (

let _55_2416 = (occurs_check env wl (u1, k1) t2)
in (match (_55_2416) with
| (occurs_ok, _55_2415) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(

let sol = (let _145_1258 = (let _145_1257 = (u_abs k1 xs t2)
in ((u1, k1), _145_1257))
in TERM (_145_1258))
in (

let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(

let _55_2427 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_55_2427) with
| (sol, (_55_2422, u2, k2, ys)) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (

let _55_2429 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _145_1259 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _145_1259))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _55_2434 -> begin
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

let _55_2439 = lhs
in (match (_55_2439) with
| (t1, u1, k1, args1) -> begin
(

let _55_2444 = rhs
in (match (_55_2444) with
| (t2, u2, k2, args2) -> begin
(

let maybe_pat_vars1 = (pat_vars env [] args1)
in (

let maybe_pat_vars2 = (pat_vars env [] args2)
in (

let r = t2.FStar_Syntax_Syntax.pos
in (match ((maybe_pat_vars1, maybe_pat_vars2)) with
| (Some (xs), Some (ys)) -> begin
(solve_both_pats wl (u1, k1, xs, args1) (u2, k2, ys, args2) t2.FStar_Syntax_Syntax.pos)
end
| (Some (xs), None) -> begin
(solve_one_pat (t1, u1, k1, xs) rhs)
end
| (None, Some (ys)) -> begin
(solve_one_pat (t2, u2, k2, ys) lhs)
end
| _55_2462 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(

let _55_2466 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_55_2466) with
| (sol, _55_2465) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (

let _55_2468 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _145_1260 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _145_1260))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _55_2473 -> begin
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
(let _145_1261 = (solve_prob orig None [] wl)
in (solve env _145_1261))
end else begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _145_1262 = (solve_prob orig None [] wl)
in (solve env _145_1262))
end else begin
(

let _55_2477 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _145_1263 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _145_1263))
end else begin
()
end
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let match_num_binders = (fun _55_2482 _55_2485 -> (match ((_55_2482, _55_2485)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(

let curry = (fun n bs mk_cod -> (

let _55_2492 = (FStar_Util.first_N n bs)
in (match (_55_2492) with
| (bs, rest) -> begin
(let _145_1293 = (mk_cod rest)
in (bs, _145_1293))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _145_1297 = (let _145_1294 = (mk_cod1 [])
in (bs1, _145_1294))
in (let _145_1296 = (let _145_1295 = (mk_cod2 [])
in (bs2, _145_1295))
in (_145_1297, _145_1296)))
end else begin
if (l1 > l2) then begin
(let _145_1300 = (curry l2 bs1 mk_cod1)
in (let _145_1299 = (let _145_1298 = (mk_cod2 [])
in (bs2, _145_1298))
in (_145_1300, _145_1299)))
end else begin
(let _145_1303 = (let _145_1301 = (mk_cod1 [])
in (bs1, _145_1301))
in (let _145_1302 = (curry l1 bs2 mk_cod2)
in (_145_1303, _145_1302)))
end
end)))
end))
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
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
(let _145_1308 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _145_1308))
end))
in (

let _55_2535 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_55_2535) with
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
in (let _145_1315 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _145_1314 -> FStar_TypeChecker_Common.CProb (_145_1314)) _145_1315)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l _55_27 -> (match (_55_27) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((bs, t, l))) None t.FStar_Syntax_Syntax.pos)
end))
in (

let _55_2565 = (match_num_binders (bs1, (mk_t tbody1 lopt1)) (bs2, (mk_t tbody2 lopt2)))
in (match (_55_2565) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _145_1330 = (let _145_1329 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _145_1328 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _145_1329 problem.FStar_TypeChecker_Common.relation _145_1328 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _145_1327 -> FStar_TypeChecker_Common.TProb (_145_1327)) _145_1330))))
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_55_2570), FStar_Syntax_Syntax.Tm_refine (_55_2573)) -> begin
(

let _55_2578 = (as_refinement env wl t1)
in (match (_55_2578) with
| (x1, phi1) -> begin
(

let _55_2581 = (as_refinement env wl t2)
in (match (_55_2581) with
| (x2, phi2) -> begin
(

let base_prob = (let _145_1332 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _145_1331 -> FStar_TypeChecker_Common.TProb (_145_1331)) _145_1332))
in (

let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (

let subst = (FStar_Syntax_Syntax.DB ((0, x1)))::[]
in (

let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (

let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (

let env = (FStar_TypeChecker_Env.push_bv env x1)
in (

let mk_imp = (fun imp phi1 phi2 -> (let _145_1349 = (imp phi1 phi2)
in (FStar_All.pipe_right _145_1349 (guard_on_element problem x1))))
in (

let fallback = (fun _55_2593 -> (match (()) with
| () -> begin
(

let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (

let guard = (let _145_1352 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _145_1352 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(

let ref_prob = (let _145_1356 = (let _145_1355 = (let _145_1354 = (FStar_Syntax_Syntax.mk_binder x1)
in (_145_1354)::(p_scope orig))
in (mk_problem _145_1355 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _145_1353 -> FStar_TypeChecker_Common.TProb (_145_1353)) _145_1356))
in (match ((solve env (

let _55_2598 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _55_2598.ctr; defer_ok = false; smt_ok = _55_2598.smt_ok; tcenv = _55_2598.tcenv}))) with
| Failed (_55_2601) -> begin
(fallback ())
end
| Success (_55_2604) -> begin
(

let guard = (let _145_1359 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _145_1358 = (let _145_1357 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _145_1357 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _145_1359 _145_1358)))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (

let wl = (

let _55_2608 = wl
in {attempting = _55_2608.attempting; wl_deferred = _55_2608.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _55_2608.defer_ok; smt_ok = _55_2608.smt_ok; tcenv = _55_2608.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _145_1361 = (destruct_flex_t t1)
in (let _145_1360 = (destruct_flex_t t2)
in (flex_flex orig _145_1361 _145_1360)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _145_1362 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _145_1362 t2 wl))
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
in if (let _145_1363 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _145_1363)) then begin
(let _145_1366 = (FStar_All.pipe_left (fun _145_1364 -> FStar_TypeChecker_Common.TProb (_145_1364)) (

let _55_2753 = problem
in {FStar_TypeChecker_Common.pid = _55_2753.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2753.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _55_2753.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2753.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2753.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2753.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2753.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2753.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2753.FStar_TypeChecker_Common.rank}))
in (let _145_1365 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _145_1366 _145_1365 t2 wl)))
end else begin
(

let _55_2757 = (base_and_refinement env wl t2)
in (match (_55_2757) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _145_1369 = (FStar_All.pipe_left (fun _145_1367 -> FStar_TypeChecker_Common.TProb (_145_1367)) (

let _55_2759 = problem
in {FStar_TypeChecker_Common.pid = _55_2759.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2759.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _55_2759.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2759.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2759.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2759.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2759.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2759.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2759.FStar_TypeChecker_Common.rank}))
in (let _145_1368 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _145_1369 _145_1368 t_base wl)))
end
| Some (y, phi) -> begin
(

let y' = (

let _55_2765 = y
in {FStar_Syntax_Syntax.ppname = _55_2765.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_2765.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element problem y' phi)
in (

let base_prob = (let _145_1371 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _145_1370 -> FStar_TypeChecker_Common.TProb (_145_1370)) _145_1371))
in (

let guard = (let _145_1372 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _145_1372 impl))
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

let _55_2798 = (base_and_refinement env wl t1)
in (match (_55_2798) with
| (t_base, _55_2797) -> begin
(solve_t env (

let _55_2799 = problem
in {FStar_TypeChecker_Common.pid = _55_2799.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _55_2799.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2799.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2799.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2799.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2799.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2799.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2799.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_55_2802), _55_2805) -> begin
(

let t2 = (let _145_1373 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _145_1373))
in (solve_t env (

let _55_2808 = problem
in {FStar_TypeChecker_Common.pid = _55_2808.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2808.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_2808.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_2808.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2808.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2808.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2808.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2808.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2808.FStar_TypeChecker_Common.rank}) wl))
end
| (_55_2811, FStar_Syntax_Syntax.Tm_refine (_55_2813)) -> begin
(

let t1 = (let _145_1374 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _145_1374))
in (solve_t env (

let _55_2817 = problem
in {FStar_TypeChecker_Common.pid = _55_2817.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_2817.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_2817.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2817.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2817.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2817.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2817.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2817.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2817.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(

let maybe_eta = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_55_2834) -> begin
t
end
| _55_2837 -> begin
(FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
end))
in (let _145_1379 = (

let _55_2838 = problem
in (let _145_1378 = (maybe_eta t1)
in (let _145_1377 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _55_2838.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _145_1378; FStar_TypeChecker_Common.relation = _55_2838.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _145_1377; FStar_TypeChecker_Common.element = _55_2838.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2838.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2838.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2838.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2838.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2838.FStar_TypeChecker_Common.rank})))
in (solve_t env _145_1379 wl)))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(

let head1 = (let _145_1380 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _145_1380 Prims.fst))
in (

let head2 = (let _145_1381 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _145_1381 Prims.fst))
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
(let _145_1383 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _145_1382 -> Some (_145_1382)) _145_1383))
end
in (let _145_1384 = (solve_prob orig guard [] wl)
in (solve env _145_1384)))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _55_2919, _55_2921), _55_2925) -> begin
(solve_t' env (

let _55_2927 = problem
in {FStar_TypeChecker_Common.pid = _55_2927.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_2927.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_2927.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2927.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2927.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2927.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2927.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2927.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2927.FStar_TypeChecker_Common.rank}) wl)
end
| (_55_2930, FStar_Syntax_Syntax.Tm_ascribed (t2, _55_2933, _55_2935)) -> begin
(solve_t' env (

let _55_2939 = problem
in {FStar_TypeChecker_Common.pid = _55_2939.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2939.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_2939.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_2939.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2939.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2939.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2939.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2939.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2939.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _145_1387 = (let _145_1386 = (FStar_Syntax_Print.tag_of_term t1)
in (let _145_1385 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _145_1386 _145_1385)))
in (FStar_All.failwith _145_1387))
end
| _55_2978 -> begin
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

let _55_2995 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (

let sub_probs = (FStar_List.map2 (fun _55_3000 _55_3004 -> (match ((_55_3000, _55_3004)) with
| ((a1, _55_2999), (a2, _55_3003)) -> begin
(let _145_1402 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _145_1401 -> FStar_TypeChecker_Common.TProb (_145_1401)) _145_1402))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (let _145_1404 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _145_1404))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in (

let solve_sub = (fun c1 edge c2 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(

let wp = (match (c1.FStar_Syntax_Syntax.effect_args) with
| ((wp1, _55_3016))::[] -> begin
wp1
end
| _55_3020 -> begin
(let _145_1412 = (let _145_1411 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _145_1411))
in (FStar_All.failwith _145_1412))
end)
in (

let c1 = (let _145_1415 = (let _145_1414 = (let _145_1413 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _145_1413))
in (_145_1414)::[])
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _145_1415; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2)))
end else begin
(

let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _55_28 -> (match (_55_28) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _55_3028 -> begin
false
end))))
in (

let _55_3049 = (match ((c1.FStar_Syntax_Syntax.effect_args, c2.FStar_Syntax_Syntax.effect_args)) with
| (((wp1, _55_3034))::_55_3031, ((wp2, _55_3041))::_55_3038) -> begin
(wp1, wp2)
end
| _55_3046 -> begin
(let _145_1419 = (let _145_1418 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _145_1417 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _145_1418 _145_1417)))
in (FStar_All.failwith _145_1419))
end)
in (match (_55_3049) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _145_1420 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _145_1420 wl))
end else begin
(

let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let g = if is_null_wp_2 then begin
(

let _55_3051 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _145_1430 = (let _145_1429 = (let _145_1428 = (let _145_1422 = (let _145_1421 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_145_1421)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _145_1422 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _145_1427 = (let _145_1426 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _145_1425 = (let _145_1424 = (let _145_1423 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_1423))
in (_145_1424)::[])
in (_145_1426)::_145_1425))
in (_145_1428, _145_1427)))
in FStar_Syntax_Syntax.Tm_app (_145_1429))
in (FStar_Syntax_Syntax.mk _145_1430 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(let _145_1442 = (let _145_1441 = (let _145_1440 = (let _145_1432 = (let _145_1431 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_145_1431)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _145_1432 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (let _145_1439 = (let _145_1438 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _145_1437 = (let _145_1436 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _145_1435 = (let _145_1434 = (let _145_1433 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_1433))
in (_145_1434)::[])
in (_145_1436)::_145_1435))
in (_145_1438)::_145_1437))
in (_145_1440, _145_1439)))
in FStar_Syntax_Syntax.Tm_app (_145_1441))
in (FStar_Syntax_Syntax.mk _145_1442 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r))
end
in (

let base_prob = (let _145_1444 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _145_1443 -> FStar_TypeChecker_Common.TProb (_145_1443)) _145_1444))
in (

let wl = (let _145_1448 = (let _145_1447 = (let _145_1446 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _145_1446 g))
in (FStar_All.pipe_left (fun _145_1445 -> Some (_145_1445)) _145_1447))
in (solve_prob orig _145_1448 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end
end)))
end))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _145_1449 = (solve_prob orig None [] wl)
in (solve env _145_1449))
end else begin
(

let _55_3056 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1451 = (FStar_Syntax_Print.comp_to_string c1)
in (let _145_1450 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _145_1451 (rel_to_string problem.FStar_TypeChecker_Common.relation) _145_1450)))
end else begin
()
end
in (

let _55_3060 = (let _145_1453 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (let _145_1452 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in (_145_1453, _145_1452)))
in (match (_55_3060) with
| (c1, c2) -> begin
(match ((c1.FStar_Syntax_Syntax.n, c2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.Total (t2)) when (FStar_Syntax_Util.non_informative t2) -> begin
(let _145_1454 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _145_1454 wl))
end
| (FStar_Syntax_Syntax.GTotal (_55_3067), FStar_Syntax_Syntax.Total (_55_3070)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _145_1455 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _145_1455 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _145_1457 = (

let _55_3098 = problem
in (let _145_1456 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _55_3098.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _145_1456; FStar_TypeChecker_Common.relation = _55_3098.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_3098.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_3098.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3098.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3098.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3098.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3098.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3098.FStar_TypeChecker_Common.rank}))
in (solve_c env _145_1457 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _145_1459 = (

let _55_3114 = problem
in (let _145_1458 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _55_3114.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_3114.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_3114.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _145_1458; FStar_TypeChecker_Common.element = _55_3114.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3114.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3114.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3114.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3114.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3114.FStar_TypeChecker_Common.rank}))
in (solve_c env _145_1459 wl))
end
| (FStar_Syntax_Syntax.Comp (_55_3117), FStar_Syntax_Syntax.Comp (_55_3120)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _145_1460 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _145_1460 wl))
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

let _55_3127 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
if (((FStar_Syntax_Util.is_ghost_effect c1.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c2.FStar_Syntax_Syntax.effect_name)) && (let _145_1461 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c2.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative _145_1461))) then begin
(

let edge = {FStar_TypeChecker_Env.msource = c1.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c2.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = (fun r t -> t)}
in (solve_sub c1 edge c2))
end else begin
(let _145_1466 = (let _145_1465 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _145_1464 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _145_1465 _145_1464)))
in (giveup env _145_1466 orig))
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


let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _145_1470 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _55_3147 -> (match (_55_3147) with
| (_55_3137, _55_3139, u, _55_3142, _55_3144, _55_3146) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _145_1470 (FStar_String.concat ", "))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match ((g.FStar_TypeChecker_Env.guard_f, g.FStar_TypeChecker_Env.deferred)) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _55_3154 -> begin
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

let carry = (let _145_1476 = (FStar_List.map (fun _55_3162 -> (match (_55_3162) with
| (_55_3160, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _145_1476 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))


let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _55_3171; FStar_TypeChecker_Env.implicits = _55_3169} -> begin
true
end
| _55_3176 -> begin
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
| _55_3194 -> begin
(FStar_All.failwith "impossible")
end)
in (let _145_1497 = (

let _55_3196 = g
in (let _145_1496 = (let _145_1495 = (let _145_1494 = (let _145_1488 = (FStar_Syntax_Syntax.mk_binder x)
in (_145_1488)::[])
in (let _145_1493 = (let _145_1492 = (let _145_1491 = (let _145_1489 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _145_1489 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _145_1491 (fun _145_1490 -> FStar_Util.Inl (_145_1490))))
in Some (_145_1492))
in (FStar_Syntax_Util.abs _145_1494 f _145_1493)))
in (FStar_All.pipe_left (fun _145_1487 -> FStar_TypeChecker_Common.NonTrivial (_145_1487)) _145_1495))
in {FStar_TypeChecker_Env.guard_f = _145_1496; FStar_TypeChecker_Env.deferred = _55_3196.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3196.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3196.FStar_TypeChecker_Env.implicits}))
in Some (_145_1497)))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _55_3203 = g
in (let _145_1508 = (let _145_1507 = (let _145_1506 = (let _145_1505 = (let _145_1504 = (let _145_1503 = (FStar_Syntax_Syntax.as_arg e)
in (_145_1503)::[])
in (f, _145_1504))
in FStar_Syntax_Syntax.Tm_app (_145_1505))
in (FStar_Syntax_Syntax.mk _145_1506 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _145_1502 -> FStar_TypeChecker_Common.NonTrivial (_145_1502)) _145_1507))
in {FStar_TypeChecker_Env.guard_f = _145_1508; FStar_TypeChecker_Env.deferred = _55_3203.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3203.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3203.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_55_3208) -> begin
(FStar_All.failwith "impossible")
end))


let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _145_1515 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_145_1515))
end))


let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _55_3226 -> begin
FStar_TypeChecker_Common.NonTrivial (t)
end))


let imp_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
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


let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _145_1538 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _145_1538; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _55_3253 = g
in (let _145_1553 = (let _145_1552 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _145_1552 (fun _145_1551 -> FStar_TypeChecker_Common.NonTrivial (_145_1551))))
in {FStar_TypeChecker_Env.guard_f = _145_1553; FStar_TypeChecker_Env.deferred = _55_3253.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3253.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3253.FStar_TypeChecker_Env.implicits}))
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _145_1561 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _145_1560 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _145_1561 (rel_to_string rel) _145_1560)))
end else begin
"TOP"
end
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (let _145_1572 = (let _145_1571 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _145_1570 -> Some (_145_1570)) _145_1571))
in (FStar_Syntax_Syntax.new_bv _145_1572 t1))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (let _145_1576 = (let _145_1574 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _145_1573 -> Some (_145_1573)) _145_1574))
in (let _145_1575 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _145_1576 _145_1575)))
in (FStar_TypeChecker_Common.TProb (p), x)))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (

let probs = if (FStar_Options.eager_inference ()) then begin
(

let _55_3273 = probs
in {attempting = _55_3273.attempting; wl_deferred = _55_3273.wl_deferred; ctr = _55_3273.ctr; defer_ok = false; smt_ok = _55_3273.smt_ok; tcenv = _55_3273.tcenv})
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

let _55_3280 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(

let _55_3286 = (FStar_Unionfind.rollback tx)
in (

let _55_3288 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _145_1588 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _145_1588))
end else begin
()
end
in (err (d, s))))
end)))))


let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _55_3295 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _145_1593 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _145_1593))
end else begin
()
end
in (

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (

let _55_3298 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _145_1594 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _145_1594))
end else begin
()
end
in (

let f = (match ((let _145_1595 = (FStar_Syntax_Util.unmeta f)
in _145_1595.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _55_3303 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (

let _55_3305 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _55_3305.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3305.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3305.FStar_TypeChecker_Env.implicits})))))
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _145_1607 = (let _145_1606 = (let _145_1605 = (let _145_1604 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _145_1604 (fun _145_1603 -> FStar_TypeChecker_Common.NonTrivial (_145_1603))))
in {FStar_TypeChecker_Env.guard_f = _145_1605; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _145_1606))
in (FStar_All.pipe_left (fun _145_1602 -> Some (_145_1602)) _145_1607))
end))


let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (

let _55_3316 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1615 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_1614 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _145_1615 _145_1614)))
end else begin
()
end
in (

let prob = (let _145_1618 = (let _145_1617 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _145_1617))
in (FStar_All.pipe_left (fun _145_1616 -> FStar_TypeChecker_Common.TProb (_145_1616)) _145_1618))
in (

let g = (let _145_1620 = (solve_and_commit env (singleton env prob) (fun _55_3319 -> None))
in (FStar_All.pipe_left (with_guard env prob) _145_1620))
in g))))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _145_1630 = (let _145_1629 = (let _145_1628 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _145_1627 = (FStar_TypeChecker_Env.get_range env)
in (_145_1628, _145_1627)))
in FStar_Syntax_Syntax.Error (_145_1629))
in (Prims.raise _145_1630))
end
| Some (g) -> begin
(

let _55_3328 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1633 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_1632 = (FStar_Syntax_Print.term_to_string t2)
in (let _145_1631 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _145_1633 _145_1632 _145_1631))))
end else begin
()
end
in g)
end))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (

let _55_3333 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1641 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _145_1640 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _145_1641 _145_1640)))
end else begin
()
end
in (

let _55_3337 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_55_3337) with
| (prob, x) -> begin
(

let g = (let _145_1643 = (solve_and_commit env (singleton env prob) (fun _55_3338 -> None))
in (FStar_All.pipe_left (with_guard env prob) _145_1643))
in (

let _55_3341 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _145_1647 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _145_1646 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _145_1645 = (let _145_1644 = (FStar_Util.must g)
in (guard_to_string env _145_1644))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _145_1647 _145_1646 _145_1645))))
end else begin
()
end
in (abstract_guard x g)))
end))))


let subtype_fail = (fun env t1 t2 -> (let _145_1654 = (let _145_1653 = (let _145_1652 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _145_1651 = (FStar_TypeChecker_Env.get_range env)
in (_145_1652, _145_1651)))
in FStar_Syntax_Syntax.Error (_145_1653))
in (Prims.raise _145_1654)))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (

let _55_3349 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1662 = (FStar_Syntax_Print.comp_to_string c1)
in (let _145_1661 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _145_1662 _145_1661)))
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

let prob = (let _145_1665 = (let _145_1664 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _145_1664 "sub_comp"))
in (FStar_All.pipe_left (fun _145_1663 -> FStar_TypeChecker_Common.CProb (_145_1663)) _145_1665))
in (let _145_1667 = (solve_and_commit env (singleton env prob) (fun _55_3353 -> None))
in (FStar_All.pipe_left (with_guard env prob) _145_1667))))))


let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (

let fail = (fun msg u1 u2 -> (

let _55_3362 = (FStar_Unionfind.rollback tx)
in (

let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _145_1685 = (let _145_1684 = (let _145_1683 = (let _145_1681 = (FStar_Syntax_Print.univ_to_string u1)
in (let _145_1680 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _145_1681 _145_1680 msg)))
in (let _145_1682 = (FStar_TypeChecker_Env.get_range env)
in (_145_1683, _145_1682)))
in FStar_Syntax_Syntax.Error (_145_1684))
in (Prims.raise _145_1685)))))
in (

let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
((uv, (u1)::[]))::[]
end
| (hd)::tl -> begin
(

let _55_3378 = hd
in (match (_55_3378) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
((uv', (u1)::lower_bounds))::tl
end else begin
(let _145_1692 = (insert uv u1 tl)
in (hd)::_145_1692)
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
(let _145_1697 = (insert uv u1 out)
in (group_by _145_1697 rest))
end)
end
| _55_3393 -> begin
None
end))
end))
in (

let ad_hoc_fallback = (fun _55_3395 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _55_3398 -> begin
(

let wl = (

let _55_3399 = (empty_worklist env)
in {attempting = _55_3399.attempting; wl_deferred = _55_3399.wl_deferred; ctr = _55_3399.ctr; defer_ok = true; smt_ok = _55_3399.smt_ok; tcenv = _55_3399.tcenv})
in (FStar_All.pipe_right ineqs (FStar_List.iter (fun _55_3404 -> (match (_55_3404) with
| (u1, u2) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _55_3409 -> begin
(match ((solve_universe_eq (- (1)) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(

let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _55_3419 -> begin
(u1)::[]
end)
in (

let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _55_3424 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _55_29 -> (match (_55_29) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(

let _55_3431 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_3431) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (

let _55_3435 = (FStar_Syntax_Util.univ_kernel u')
in (match (_55_3435) with
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
| USolved (_55_3437) -> begin
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

let _55_3441 = (empty_worklist env)
in {attempting = _55_3441.attempting; wl_deferred = _55_3441.wl_deferred; ctr = _55_3441.ctr; defer_ok = false; smt_ok = _55_3441.smt_ok; tcenv = _55_3441.tcenv})
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
| _55_3456 -> begin
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

let _55_3461 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail = (fun _55_3468 -> (match (_55_3468) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error ((msg, (p_loc d))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (

let _55_3471 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_1718 = (wl_to_string wl)
in (let _145_1717 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _145_1718 _145_1717)))
end else begin
()
end
in (

let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(

let _55_3475 = g
in {FStar_TypeChecker_Env.guard_f = _55_3475.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _55_3475.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3475.FStar_TypeChecker_Env.implicits})
end
| _55_3478 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (

let _55_3480 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (

let _55_3482 = g
in {FStar_TypeChecker_Env.guard_f = _55_3482.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3482.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _55_3482.FStar_TypeChecker_Env.implicits})))))))


let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun use_env_range_msg env g -> (

let g = (solve_deferred_constraints env g)
in (

let _55_3497 = if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
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

let _55_3495 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1735 = (FStar_TypeChecker_Env.get_range env)
in (let _145_1734 = (let _145_1733 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _145_1733))
in (FStar_TypeChecker_Errors.diag _145_1735 _145_1734)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc))
end))
end)
end
in (

let _55_3499 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _55_3499.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3499.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3499.FStar_TypeChecker_Env.implicits}))))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (discharge_guard' None env g))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (

let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _55_3508 -> begin
false
end))
in (

let rec until_fixpoint = (fun _55_3512 implicits -> (match (_55_3512) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
if (not (changed)) then begin
out
end else begin
(until_fixpoint ([], false) out)
end
end
| (hd)::tl -> begin
(

let _55_3525 = hd
in (match (_55_3525) with
| (_55_3519, env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint ((hd)::out, changed) tl)
end else begin
(

let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (

let _55_3528 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_1751 = (FStar_Syntax_Print.uvar_to_string u)
in (let _145_1750 = (FStar_Syntax_Print.term_to_string tm)
in (let _145_1749 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _145_1751 _145_1750 _145_1749))))
end else begin
()
end
in (

let _55_3537 = (env.FStar_TypeChecker_Env.type_of (

let _55_3530 = env
in {FStar_TypeChecker_Env.solver = _55_3530.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _55_3530.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _55_3530.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _55_3530.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _55_3530.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _55_3530.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _55_3530.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _55_3530.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _55_3530.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _55_3530.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _55_3530.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _55_3530.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _55_3530.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _55_3530.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _55_3530.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _55_3530.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _55_3530.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _55_3530.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _55_3530.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _55_3530.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_55_3537) with
| (_55_3533, _55_3535, g) -> begin
(

let g = if env.FStar_TypeChecker_Env.is_pattern then begin
(

let _55_3538 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _55_3538.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3538.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3538.FStar_TypeChecker_Env.implicits})
end else begin
g
end
in (

let g' = (discharge_guard' (Some ((fun _55_3541 -> (match (()) with
| () -> begin
(FStar_Syntax_Print.term_to_string tm)
end)))) env g)
in (until_fixpoint ((FStar_List.append g'.FStar_TypeChecker_Env.implicits out), true) tl)))
end)))))
end
end))
end)
end))
in (

let _55_3543 = g
in (let _145_1755 = (until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _55_3543.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3543.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3543.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _145_1755})))))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g = (let _145_1760 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _145_1760 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _145_1761 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _145_1761))
end
| ((reason, _55_3553, _55_3555, e, t, r))::_55_3550 -> begin
(let _145_1766 = (let _145_1765 = (let _145_1764 = (let _145_1763 = (FStar_Syntax_Print.term_to_string t)
in (let _145_1762 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" _145_1763 _145_1762 reason)))
in (_145_1764, r))
in FStar_Syntax_Syntax.Error (_145_1765))
in (Prims.raise _145_1766))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let _55_3563 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _55_3563.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3563.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((u1, u2))::[]; FStar_TypeChecker_Env.implicits = _55_3563.FStar_TypeChecker_Env.implicits}))




