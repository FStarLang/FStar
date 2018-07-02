
open Prims
open FStar_Pervasives
type rel =
| EQ
| SUB
| SUBINV


let uu___is_EQ : rel  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EQ -> begin
true
end
| uu____6 -> begin
false
end))


let uu___is_SUB : rel  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SUB -> begin
true
end
| uu____12 -> begin
false
end))


let uu___is_SUBINV : rel  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SUBINV -> begin
true
end
| uu____18 -> begin
false
end))

type rank_t =
| Rigid_rigid
| Flex_rigid_eq
| Flex_flex_pattern_eq
| Flex_rigid
| Rigid_flex
| Flex_flex


let uu___is_Rigid_rigid : rank_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Rigid_rigid -> begin
true
end
| uu____24 -> begin
false
end))


let uu___is_Flex_rigid_eq : rank_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Flex_rigid_eq -> begin
true
end
| uu____30 -> begin
false
end))


let uu___is_Flex_flex_pattern_eq : rank_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Flex_flex_pattern_eq -> begin
true
end
| uu____36 -> begin
false
end))


let uu___is_Flex_rigid : rank_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Flex_rigid -> begin
true
end
| uu____42 -> begin
false
end))


let uu___is_Rigid_flex : rank_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Rigid_flex -> begin
true
end
| uu____48 -> begin
false
end))


let uu___is_Flex_flex : rank_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Flex_flex -> begin
true
end
| uu____54 -> begin
false
end))

type 'a problem =
{pid : Prims.int; lhs : 'a; relation : rel; rhs : 'a; element : FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option; logical_guard : FStar_Syntax_Syntax.term; logical_guard_uvar : FStar_Syntax_Syntax.ctx_uvar; reason : Prims.string Prims.list; loc : FStar_Range.range; rank : rank_t FStar_Pervasives_Native.option}


let __proj__Mkproblem__item__pid : 'a . 'a problem  ->  Prims.int = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__pid
end))


let __proj__Mkproblem__item__lhs : 'a . 'a problem  ->  'a = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__lhs
end))


let __proj__Mkproblem__item__relation : 'a . 'a problem  ->  rel = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__relation
end))


let __proj__Mkproblem__item__rhs : 'a . 'a problem  ->  'a = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__rhs
end))


let __proj__Mkproblem__item__element : 'a . 'a problem  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__element
end))


let __proj__Mkproblem__item__logical_guard : 'a . 'a problem  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__logical_guard
end))


let __proj__Mkproblem__item__logical_guard_uvar : 'a . 'a problem  ->  FStar_Syntax_Syntax.ctx_uvar = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__logical_guard_uvar
end))


let __proj__Mkproblem__item__reason : 'a . 'a problem  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__reason
end))


let __proj__Mkproblem__item__loc : 'a . 'a problem  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__loc
end))


let __proj__Mkproblem__item__rank : 'a . 'a problem  ->  rank_t FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__rank
end))

type prob =
| TProb of FStar_Syntax_Syntax.typ problem
| CProb of FStar_Syntax_Syntax.comp problem


let uu___is_TProb : prob  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TProb (_0) -> begin
true
end
| uu____443 -> begin
false
end))


let __proj__TProb__item___0 : prob  ->  FStar_Syntax_Syntax.typ problem = (fun projectee -> (match (projectee) with
| TProb (_0) -> begin
_0
end))


let uu___is_CProb : prob  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CProb (_0) -> begin
true
end
| uu____465 -> begin
false
end))


let __proj__CProb__item___0 : prob  ->  FStar_Syntax_Syntax.comp problem = (fun projectee -> (match (projectee) with
| CProb (_0) -> begin
_0
end))


let as_tprob : prob  ->  FStar_Syntax_Syntax.typ problem = (fun uu___207_485 -> (match (uu___207_485) with
| TProb (p) -> begin
p
end
| uu____491 -> begin
(failwith "Expected a TProb")
end))


type probs =
prob Prims.list

type guard_formula =
| Trivial
| NonTrivial of FStar_Syntax_Syntax.formula


let uu___is_Trivial : guard_formula  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Trivial -> begin
true
end
| uu____506 -> begin
false
end))


let uu___is_NonTrivial : guard_formula  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonTrivial (_0) -> begin
true
end
| uu____513 -> begin
false
end))


let __proj__NonTrivial__item___0 : guard_formula  ->  FStar_Syntax_Syntax.formula = (fun projectee -> (match (projectee) with
| NonTrivial (_0) -> begin
_0
end))


type deferred =
(Prims.string * prob) Prims.list


type univ_ineq =
(FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)


let mk_by_tactic : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun tac f -> (

let t_by_tactic = (

let uu____542 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____542 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let t_reify_tactic = (

let uu____544 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.reify_tactic_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____544 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let tac1 = (

let uu____548 = (

let uu____553 = (

let uu____554 = (FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit)
in (

let uu____563 = (

let uu____574 = (FStar_Syntax_Syntax.as_arg tac)
in (uu____574)::[])
in (uu____554)::uu____563))
in (FStar_Syntax_Syntax.mk_Tm_app t_reify_tactic uu____553))
in (uu____548 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let uu____609 = (

let uu____614 = (

let uu____615 = (FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit)
in (

let uu____624 = (

let uu____635 = (FStar_Syntax_Syntax.as_arg tac1)
in (

let uu____644 = (

let uu____655 = (FStar_Syntax_Syntax.as_arg f)
in (uu____655)::[])
in (uu____635)::uu____644))
in (uu____615)::uu____624))
in (FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____614))
in (uu____609 FStar_Pervasives_Native.None FStar_Range.dummyRange))))))


let rec delta_depth_greater_than : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth  ->  Prims.bool = (fun l m -> (match (((l), (m))) with
| (FStar_Syntax_Syntax.Delta_equational_at_level (i), FStar_Syntax_Syntax.Delta_equational_at_level (j)) -> begin
(i > j)
end
| (FStar_Syntax_Syntax.Delta_constant_at_level (i), FStar_Syntax_Syntax.Delta_constant_at_level (j)) -> begin
(i > j)
end
| (FStar_Syntax_Syntax.Delta_abstract (d), uu____713) -> begin
(delta_depth_greater_than d m)
end
| (uu____714, FStar_Syntax_Syntax.Delta_abstract (d)) -> begin
(delta_depth_greater_than l d)
end
| (FStar_Syntax_Syntax.Delta_equational_at_level (uu____716), uu____717) -> begin
true
end
| (uu____718, FStar_Syntax_Syntax.Delta_equational_at_level (uu____719)) -> begin
false
end))


let rec decr_delta_depth : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun uu___208_726 -> (match (uu___208_726) with
| FStar_Syntax_Syntax.Delta_constant_at_level (_0_16) when (_0_16 = (Prims.parse_int "0")) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Delta_equational_at_level (_0_17) when (_0_17 = (Prims.parse_int "0")) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Delta_constant_at_level (i) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant_at_level ((i - (Prims.parse_int "1"))))
end
| FStar_Syntax_Syntax.Delta_equational_at_level (i) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational_at_level ((i - (Prims.parse_int "1"))))
end
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(decr_delta_depth d)
end))

type identifier_info =
{identifier : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either; identifier_ty : FStar_Syntax_Syntax.typ; identifier_range : FStar_Range.range}


let __proj__Mkidentifier_info__item__identifier : identifier_info  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either = (fun projectee -> (match (projectee) with
| {identifier = __fname__identifier; identifier_ty = __fname__identifier_ty; identifier_range = __fname__identifier_range} -> begin
__fname__identifier
end))


let __proj__Mkidentifier_info__item__identifier_ty : identifier_info  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| {identifier = __fname__identifier; identifier_ty = __fname__identifier_ty; identifier_range = __fname__identifier_range} -> begin
__fname__identifier_ty
end))


let __proj__Mkidentifier_info__item__identifier_range : identifier_info  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {identifier = __fname__identifier; identifier_ty = __fname__identifier_ty; identifier_range = __fname__identifier_range} -> begin
__fname__identifier_range
end))


let insert_col_info : Prims.int  ->  identifier_info  ->  (Prims.int * identifier_info) Prims.list  ->  (Prims.int * identifier_info) Prims.list = (fun col info col_infos -> (

let rec __insert = (fun aux rest -> (match (rest) with
| [] -> begin
((aux), ((((col), (info)))::[]))
end
| ((c, i))::rest' -> begin
(match ((col < c)) with
| true -> begin
((aux), ((((col), (info)))::rest))
end
| uu____964 -> begin
(__insert ((((c), (i)))::aux) rest')
end)
end))
in (

let uu____969 = (__insert [] col_infos)
in (match (uu____969) with
| (l, r) -> begin
(FStar_List.append (FStar_List.rev l) r)
end))))


let find_nearest_preceding_col_info : Prims.int  ->  (Prims.int * identifier_info) Prims.list  ->  identifier_info FStar_Pervasives_Native.option = (fun col col_infos -> (

let rec aux = (fun out uu___209_1074 -> (match (uu___209_1074) with
| [] -> begin
out
end
| ((c, i))::rest -> begin
(match ((c > col)) with
| true -> begin
out
end
| uu____1104 -> begin
(aux (FStar_Pervasives_Native.Some (i)) rest)
end)
end))
in (aux FStar_Pervasives_Native.None col_infos)))


type id_info_by_col =
(Prims.int * identifier_info) Prims.list


type col_info_by_row =
id_info_by_col FStar_Util.pimap


type row_info_by_file =
col_info_by_row FStar_Util.psmap

type id_info_table =
{id_info_enabled : Prims.bool; id_info_db : row_info_by_file; id_info_buffer : identifier_info Prims.list}


let __proj__Mkid_info_table__item__id_info_enabled : id_info_table  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {id_info_enabled = __fname__id_info_enabled; id_info_db = __fname__id_info_db; id_info_buffer = __fname__id_info_buffer} -> begin
__fname__id_info_enabled
end))


let __proj__Mkid_info_table__item__id_info_db : id_info_table  ->  row_info_by_file = (fun projectee -> (match (projectee) with
| {id_info_enabled = __fname__id_info_enabled; id_info_db = __fname__id_info_db; id_info_buffer = __fname__id_info_buffer} -> begin
__fname__id_info_db
end))


let __proj__Mkid_info_table__item__id_info_buffer : id_info_table  ->  identifier_info Prims.list = (fun projectee -> (match (projectee) with
| {id_info_enabled = __fname__id_info_enabled; id_info_db = __fname__id_info_db; id_info_buffer = __fname__id_info_buffer} -> begin
__fname__id_info_buffer
end))


let id_info_table_empty : id_info_table = (

let uu____1166 = (FStar_Util.psmap_empty ())
in {id_info_enabled = false; id_info_db = uu____1166; id_info_buffer = []})


let id_info__insert : (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  (Prims.int * identifier_info) Prims.list FStar_Util.pimap FStar_Util.psmap  ->  identifier_info  ->  (Prims.int * identifier_info) Prims.list FStar_Util.pimap FStar_Util.psmap = (fun ty_map db info -> (

let range = info.identifier_range
in (

let use_range1 = (

let uu____1219 = (FStar_Range.use_range range)
in (FStar_Range.set_def_range range uu____1219))
in (

let info1 = (

let uu___212_1221 = info
in (

let uu____1222 = (ty_map info.identifier_ty)
in {identifier = uu___212_1221.identifier; identifier_ty = uu____1222; identifier_range = use_range1}))
in (

let fn = (FStar_Range.file_of_range use_range1)
in (

let start = (FStar_Range.start_of_range use_range1)
in (

let uu____1225 = (

let uu____1230 = (FStar_Range.line_of_pos start)
in (

let uu____1231 = (FStar_Range.col_of_pos start)
in ((uu____1230), (uu____1231))))
in (match (uu____1225) with
| (row, col) -> begin
(

let rows = (

let uu____1253 = (FStar_Util.pimap_empty ())
in (FStar_Util.psmap_find_default db fn uu____1253))
in (

let cols = (FStar_Util.pimap_find_default rows row [])
in (

let uu____1293 = (

let uu____1302 = (insert_col_info col info1 cols)
in (FStar_All.pipe_right uu____1302 (FStar_Util.pimap_add rows row)))
in (FStar_All.pipe_right uu____1293 (FStar_Util.psmap_add db fn)))))
end))))))))


let id_info_insert : id_info_table  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  id_info_table = (fun table id1 ty range -> (

let info = {identifier = id1; identifier_ty = ty; identifier_range = range}
in (

let uu___213_1384 = table
in {id_info_enabled = uu___213_1384.id_info_enabled; id_info_db = uu___213_1384.id_info_db; id_info_buffer = (info)::table.id_info_buffer})))


let id_info_insert_bv : id_info_table  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  id_info_table = (fun table bv ty -> (match (table.id_info_enabled) with
| true -> begin
(

let uu____1400 = (FStar_Syntax_Syntax.range_of_bv bv)
in (id_info_insert table (FStar_Util.Inl (bv)) ty uu____1400))
end
| uu____1401 -> begin
table
end))


let id_info_insert_fv : id_info_table  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  id_info_table = (fun table fv ty -> (match (table.id_info_enabled) with
| true -> begin
(

let uu____1417 = (FStar_Syntax_Syntax.range_of_fv fv)
in (id_info_insert table (FStar_Util.Inr (fv)) ty uu____1417))
end
| uu____1418 -> begin
table
end))


let id_info_toggle : id_info_table  ->  Prims.bool  ->  id_info_table = (fun table enabled -> (

let uu___214_1429 = table
in (

let uu____1430 = (enabled && (FStar_Options.ide ()))
in {id_info_enabled = uu____1430; id_info_db = uu___214_1429.id_info_db; id_info_buffer = uu___214_1429.id_info_buffer})))


let id_info_promote : id_info_table  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  id_info_table = (fun table ty_map -> (

let uu___215_1446 = table
in (

let uu____1447 = (FStar_List.fold_left (id_info__insert ty_map) table.id_info_db table.id_info_buffer)
in {id_info_enabled = uu___215_1446.id_info_enabled; id_info_db = uu____1447; id_info_buffer = []})))


let id_info_at_pos : id_info_table  ->  Prims.string  ->  Prims.int  ->  Prims.int  ->  identifier_info FStar_Pervasives_Native.option = (fun table fn row col -> (

let rows = (

let uu____1483 = (FStar_Util.pimap_empty ())
in (FStar_Util.psmap_find_default table.id_info_db fn uu____1483))
in (

let cols = (FStar_Util.pimap_find_default rows row [])
in (

let uu____1489 = (find_nearest_preceding_col_info col cols)
in (match (uu____1489) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (info) -> begin
(

let last_col = (

let uu____1496 = (FStar_Range.end_of_range info.identifier_range)
in (FStar_Range.col_of_pos uu____1496))
in (match ((col <= last_col)) with
| true -> begin
FStar_Pervasives_Native.Some (info)
end
| uu____1499 -> begin
FStar_Pervasives_Native.None
end))
end)))))


let check_uvar_ctx_invariant : Prims.string  ->  FStar_Range.range  ->  Prims.bool  ->  FStar_Syntax_Syntax.gamma  ->  FStar_Syntax_Syntax.binders  ->  unit = (fun reason r should_check g bs -> (

let print_gamma = (fun gamma -> (

let uu____1535 = (FStar_All.pipe_right gamma (FStar_List.map (fun uu___210_1545 -> (match (uu___210_1545) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let uu____1547 = (FStar_Syntax_Print.bv_to_string x)
in (Prims.strcat "Binding_var " uu____1547))
end
| FStar_Syntax_Syntax.Binding_univ (u) -> begin
(Prims.strcat "Binding_univ " u.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.Binding_lid (l, uu____1550) -> begin
(

let uu____1567 = (FStar_Ident.string_of_lid l)
in (Prims.strcat "Binding_lid " uu____1567))
end))))
in (FStar_All.pipe_right uu____1535 (FStar_String.concat "::\n"))))
in (

let fail1 = (fun uu____1575 -> (

let uu____1576 = (

let uu____1577 = (FStar_Range.string_of_range r)
in (

let uu____1578 = (print_gamma g)
in (

let uu____1579 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.format5 "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n" reason uu____1577 (match (should_check) with
| true -> begin
"true"
end
| uu____1580 -> begin
"false"
end) uu____1578 uu____1579))))
in (failwith uu____1576)))
in (match ((not (should_check))) with
| true -> begin
()
end
| uu____1581 -> begin
(

let uu____1582 = (

let uu____1607 = (FStar_Util.prefix_until (fun uu___211_1622 -> (match (uu___211_1622) with
| FStar_Syntax_Syntax.Binding_var (uu____1623) -> begin
true
end
| uu____1624 -> begin
false
end)) g)
in ((uu____1607), (bs)))
in (match (uu____1582) with
| (FStar_Pervasives_Native.None, []) -> begin
()
end
| (FStar_Pervasives_Native.Some (uu____1681, hd1, gamma_tail), (uu____1684)::uu____1685) -> begin
(

let uu____1744 = (FStar_Util.prefix bs)
in (match (uu____1744) with
| (uu____1769, (x, uu____1771)) -> begin
(match (hd1) with
| FStar_Syntax_Syntax.Binding_var (x') when (FStar_Syntax_Syntax.bv_eq x x') -> begin
()
end
| uu____1799 -> begin
(fail1 ())
end)
end))
end
| uu____1800 -> begin
(fail1 ())
end))
end))))




