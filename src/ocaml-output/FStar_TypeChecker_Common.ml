
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
| uu____25 -> begin
false
end))


let uu___is_SUB : rel  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SUB -> begin
true
end
| uu____36 -> begin
false
end))


let uu___is_SUBINV : rel  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SUBINV -> begin
true
end
| uu____47 -> begin
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
| uu____58 -> begin
false
end))


let uu___is_Flex_rigid_eq : rank_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Flex_rigid_eq -> begin
true
end
| uu____69 -> begin
false
end))


let uu___is_Flex_flex_pattern_eq : rank_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Flex_flex_pattern_eq -> begin
true
end
| uu____80 -> begin
false
end))


let uu___is_Flex_rigid : rank_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Flex_rigid -> begin
true
end
| uu____91 -> begin
false
end))


let uu___is_Rigid_flex : rank_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Rigid_flex -> begin
true
end
| uu____102 -> begin
false
end))


let uu___is_Flex_flex : rank_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Flex_flex -> begin
true
end
| uu____113 -> begin
false
end))

type 'a problem =
{pid : Prims.int; lhs : 'a; relation : rel; rhs : 'a; element : FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option; logical_guard : FStar_Syntax_Syntax.term; logical_guard_uvar : FStar_Syntax_Syntax.ctx_uvar; reason : Prims.string Prims.list; loc : FStar_Range.range; rank : rank_t FStar_Pervasives_Native.option}


let __proj__Mkproblem__item__pid : 'a . 'a problem  ->  Prims.int = (fun projectee -> (match (projectee) with
| {pid = pid; lhs = lhs; relation = relation; rhs = rhs; element = element; logical_guard = logical_guard; logical_guard_uvar = logical_guard_uvar; reason = reason; loc = loc; rank = rank} -> begin
pid
end))


let __proj__Mkproblem__item__lhs : 'a . 'a problem  ->  'a = (fun projectee -> (match (projectee) with
| {pid = pid; lhs = lhs; relation = relation; rhs = rhs; element = element; logical_guard = logical_guard; logical_guard_uvar = logical_guard_uvar; reason = reason; loc = loc; rank = rank} -> begin
lhs
end))


let __proj__Mkproblem__item__relation : 'a . 'a problem  ->  rel = (fun projectee -> (match (projectee) with
| {pid = pid; lhs = lhs; relation = relation; rhs = rhs; element = element; logical_guard = logical_guard; logical_guard_uvar = logical_guard_uvar; reason = reason; loc = loc; rank = rank} -> begin
relation
end))


let __proj__Mkproblem__item__rhs : 'a . 'a problem  ->  'a = (fun projectee -> (match (projectee) with
| {pid = pid; lhs = lhs; relation = relation; rhs = rhs; element = element; logical_guard = logical_guard; logical_guard_uvar = logical_guard_uvar; reason = reason; loc = loc; rank = rank} -> begin
rhs
end))


let __proj__Mkproblem__item__element : 'a . 'a problem  ->  FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {pid = pid; lhs = lhs; relation = relation; rhs = rhs; element = element; logical_guard = logical_guard; logical_guard_uvar = logical_guard_uvar; reason = reason; loc = loc; rank = rank} -> begin
element
end))


let __proj__Mkproblem__item__logical_guard : 'a . 'a problem  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {pid = pid; lhs = lhs; relation = relation; rhs = rhs; element = element; logical_guard = logical_guard; logical_guard_uvar = logical_guard_uvar; reason = reason; loc = loc; rank = rank} -> begin
logical_guard
end))


let __proj__Mkproblem__item__logical_guard_uvar : 'a . 'a problem  ->  FStar_Syntax_Syntax.ctx_uvar = (fun projectee -> (match (projectee) with
| {pid = pid; lhs = lhs; relation = relation; rhs = rhs; element = element; logical_guard = logical_guard; logical_guard_uvar = logical_guard_uvar; reason = reason; loc = loc; rank = rank} -> begin
logical_guard_uvar
end))


let __proj__Mkproblem__item__reason : 'a . 'a problem  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {pid = pid; lhs = lhs; relation = relation; rhs = rhs; element = element; logical_guard = logical_guard; logical_guard_uvar = logical_guard_uvar; reason = reason; loc = loc; rank = rank} -> begin
reason
end))


let __proj__Mkproblem__item__loc : 'a . 'a problem  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {pid = pid; lhs = lhs; relation = relation; rhs = rhs; element = element; logical_guard = logical_guard; logical_guard_uvar = logical_guard_uvar; reason = reason; loc = loc; rank = rank} -> begin
loc
end))


let __proj__Mkproblem__item__rank : 'a . 'a problem  ->  rank_t FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {pid = pid; lhs = lhs; relation = relation; rhs = rhs; element = element; logical_guard = logical_guard; logical_guard_uvar = logical_guard_uvar; reason = reason; loc = loc; rank = rank} -> begin
rank
end))

type prob =
| TProb of FStar_Syntax_Syntax.typ problem
| CProb of FStar_Syntax_Syntax.comp problem


let uu___is_TProb : prob  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TProb (_0) -> begin
true
end
| uu____541 -> begin
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
| uu____568 -> begin
false
end))


let __proj__CProb__item___0 : prob  ->  FStar_Syntax_Syntax.comp problem = (fun projectee -> (match (projectee) with
| CProb (_0) -> begin
_0
end))


let as_tprob : prob  ->  FStar_Syntax_Syntax.typ problem = (fun uu___0_590 -> (match (uu___0_590) with
| TProb (p) -> begin
p
end
| uu____596 -> begin
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
| uu____616 -> begin
false
end))


let uu___is_NonTrivial : guard_formula  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonTrivial (_0) -> begin
true
end
| uu____628 -> begin
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

let uu____660 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____660 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____661 = (

let uu____666 = (

let uu____667 = (FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit)
in (

let uu____676 = (

let uu____687 = (FStar_Syntax_Syntax.as_arg tac)
in (

let uu____696 = (

let uu____707 = (FStar_Syntax_Syntax.as_arg f)
in (uu____707)::[])
in (uu____687)::uu____696))
in (uu____667)::uu____676))
in (FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____666))
in (uu____661 FStar_Pervasives_Native.None FStar_Range.dummyRange))))


let rec delta_depth_greater_than : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth  ->  Prims.bool = (fun l m -> (match (((l), (m))) with
| (FStar_Syntax_Syntax.Delta_equational_at_level (i), FStar_Syntax_Syntax.Delta_equational_at_level (j)) -> begin
(i > j)
end
| (FStar_Syntax_Syntax.Delta_constant_at_level (i), FStar_Syntax_Syntax.Delta_constant_at_level (j)) -> begin
(i > j)
end
| (FStar_Syntax_Syntax.Delta_abstract (d), uu____770) -> begin
(delta_depth_greater_than d m)
end
| (uu____771, FStar_Syntax_Syntax.Delta_abstract (d)) -> begin
(delta_depth_greater_than l d)
end
| (FStar_Syntax_Syntax.Delta_equational_at_level (uu____773), uu____774) -> begin
true
end
| (uu____777, FStar_Syntax_Syntax.Delta_equational_at_level (uu____778)) -> begin
false
end))


let rec decr_delta_depth : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun uu___1_788 -> (match (uu___1_788) with
| FStar_Syntax_Syntax.Delta_constant_at_level (_791) when (_791 = (Prims.parse_int "0")) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Delta_equational_at_level (_792) when (_792 = (Prims.parse_int "0")) -> begin
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
| {identifier = identifier; identifier_ty = identifier_ty; identifier_range = identifier_range} -> begin
identifier
end))


let __proj__Mkidentifier_info__item__identifier_ty : identifier_info  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| {identifier = identifier; identifier_ty = identifier_ty; identifier_range = identifier_range} -> begin
identifier_ty
end))


let __proj__Mkidentifier_info__item__identifier_range : identifier_info  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {identifier = identifier; identifier_ty = identifier_ty; identifier_range = identifier_range} -> begin
identifier_range
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
| uu____1066 -> begin
(__insert ((((c), (i)))::aux) rest')
end)
end))
in (

let uu____1074 = (__insert [] col_infos)
in (match (uu____1074) with
| (l, r) -> begin
(FStar_List.append (FStar_List.rev l) r)
end))))


let find_nearest_preceding_col_info : Prims.int  ->  (Prims.int * identifier_info) Prims.list  ->  identifier_info FStar_Pervasives_Native.option = (fun col col_infos -> (

let rec aux = (fun out uu___2_1195 -> (match (uu___2_1195) with
| [] -> begin
out
end
| ((c, i))::rest -> begin
(match ((c > col)) with
| true -> begin
out
end
| uu____1232 -> begin
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
| {id_info_enabled = id_info_enabled; id_info_db = id_info_db; id_info_buffer = id_info_buffer} -> begin
id_info_enabled
end))


let __proj__Mkid_info_table__item__id_info_db : id_info_table  ->  row_info_by_file = (fun projectee -> (match (projectee) with
| {id_info_enabled = id_info_enabled; id_info_db = id_info_db; id_info_buffer = id_info_buffer} -> begin
id_info_db
end))


let __proj__Mkid_info_table__item__id_info_buffer : id_info_table  ->  identifier_info Prims.list = (fun projectee -> (match (projectee) with
| {id_info_enabled = id_info_enabled; id_info_db = id_info_db; id_info_buffer = id_info_buffer} -> begin
id_info_buffer
end))


let id_info_table_empty : id_info_table = (

let uu____1306 = (FStar_Util.psmap_empty ())
in {id_info_enabled = false; id_info_db = uu____1306; id_info_buffer = []})


let id_info__insert : (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  (Prims.int * identifier_info) Prims.list FStar_Util.pimap FStar_Util.psmap  ->  identifier_info  ->  (Prims.int * identifier_info) Prims.list FStar_Util.pimap FStar_Util.psmap = (fun ty_map db info -> (

let range = info.identifier_range
in (

let use_range1 = (

let uu____1364 = (FStar_Range.use_range range)
in (FStar_Range.set_def_range range uu____1364))
in (

let info1 = (

let uu___139_1366 = info
in (

let uu____1367 = (ty_map info.identifier_ty)
in {identifier = uu___139_1366.identifier; identifier_ty = uu____1367; identifier_range = use_range1}))
in (

let fn = (FStar_Range.file_of_range use_range1)
in (

let start = (FStar_Range.start_of_range use_range1)
in (

let uu____1371 = (

let uu____1378 = (FStar_Range.line_of_pos start)
in (

let uu____1380 = (FStar_Range.col_of_pos start)
in ((uu____1378), (uu____1380))))
in (match (uu____1371) with
| (row, col) -> begin
(

let rows = (

let uu____1411 = (FStar_Util.pimap_empty ())
in (FStar_Util.psmap_find_default db fn uu____1411))
in (

let cols = (FStar_Util.pimap_find_default rows row [])
in (

let uu____1457 = (

let uu____1467 = (insert_col_info col info1 cols)
in (FStar_All.pipe_right uu____1467 (FStar_Util.pimap_add rows row)))
in (FStar_All.pipe_right uu____1457 (FStar_Util.psmap_add db fn)))))
end))))))))


let id_info_insert : id_info_table  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  id_info_table = (fun table id1 ty range -> (

let info = {identifier = id1; identifier_ty = ty; identifier_range = range}
in (

let uu___154_1557 = table
in {id_info_enabled = uu___154_1557.id_info_enabled; id_info_db = uu___154_1557.id_info_db; id_info_buffer = (info)::table.id_info_buffer})))


let id_info_insert_bv : id_info_table  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  id_info_table = (fun table bv ty -> (match (table.id_info_enabled) with
| true -> begin
(

let uu____1575 = (FStar_Syntax_Syntax.range_of_bv bv)
in (id_info_insert table (FStar_Util.Inl (bv)) ty uu____1575))
end
| uu____1576 -> begin
table
end))


let id_info_insert_fv : id_info_table  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  id_info_table = (fun table fv ty -> (match (table.id_info_enabled) with
| true -> begin
(

let uu____1595 = (FStar_Syntax_Syntax.range_of_fv fv)
in (id_info_insert table (FStar_Util.Inr (fv)) ty uu____1595))
end
| uu____1596 -> begin
table
end))


let id_info_toggle : id_info_table  ->  Prims.bool  ->  id_info_table = (fun table enabled -> (

let uu___166_1611 = table
in (

let uu____1612 = (enabled && (FStar_Options.ide ()))
in {id_info_enabled = uu____1612; id_info_db = uu___166_1611.id_info_db; id_info_buffer = uu___166_1611.id_info_buffer})))


let id_info_promote : id_info_table  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  id_info_table = (fun table ty_map -> (

let uu___170_1630 = table
in (

let uu____1631 = (FStar_List.fold_left (id_info__insert ty_map) table.id_info_db table.id_info_buffer)
in {id_info_enabled = uu___170_1630.id_info_enabled; id_info_db = uu____1631; id_info_buffer = []})))


let id_info_at_pos : id_info_table  ->  Prims.string  ->  Prims.int  ->  Prims.int  ->  identifier_info FStar_Pervasives_Native.option = (fun table fn row col -> (

let rows = (

let uu____1675 = (FStar_Util.pimap_empty ())
in (FStar_Util.psmap_find_default table.id_info_db fn uu____1675))
in (

let cols = (FStar_Util.pimap_find_default rows row [])
in (

let uu____1682 = (find_nearest_preceding_col_info col cols)
in (match (uu____1682) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (info) -> begin
(

let last_col = (

let uu____1690 = (FStar_Range.end_of_range info.identifier_range)
in (FStar_Range.col_of_pos uu____1690))
in (match ((col <= last_col)) with
| true -> begin
FStar_Pervasives_Native.Some (info)
end
| uu____1694 -> begin
FStar_Pervasives_Native.None
end))
end)))))


let check_uvar_ctx_invariant : Prims.string  ->  FStar_Range.range  ->  Prims.bool  ->  FStar_Syntax_Syntax.gamma  ->  FStar_Syntax_Syntax.binders  ->  unit = (fun reason r should_check g bs -> (

let print_gamma = (fun gamma -> (

let uu____1737 = (FStar_All.pipe_right gamma (FStar_List.map (fun uu___3_1750 -> (match (uu___3_1750) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let uu____1753 = (FStar_Syntax_Print.bv_to_string x)
in (Prims.op_Hat "Binding_var " uu____1753))
end
| FStar_Syntax_Syntax.Binding_univ (u) -> begin
(Prims.op_Hat "Binding_univ " u.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.Binding_lid (l, uu____1759) -> begin
(

let uu____1776 = (FStar_Ident.string_of_lid l)
in (Prims.op_Hat "Binding_lid " uu____1776))
end))))
in (FStar_All.pipe_right uu____1737 (FStar_String.concat "::\n"))))
in (

let fail1 = (fun uu____1789 -> (

let uu____1790 = (

let uu____1792 = (FStar_Range.string_of_range r)
in (

let uu____1794 = (print_gamma g)
in (

let uu____1796 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.format5 "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n" reason uu____1792 (match (should_check) with
| true -> begin
"true"
end
| uu____1803 -> begin
"false"
end) uu____1794 uu____1796))))
in (failwith uu____1790)))
in (match ((not (should_check))) with
| true -> begin
()
end
| uu____1807 -> begin
(

let uu____1809 = (

let uu____1834 = (FStar_Util.prefix_until (fun uu___4_1849 -> (match (uu___4_1849) with
| FStar_Syntax_Syntax.Binding_var (uu____1851) -> begin
true
end
| uu____1853 -> begin
false
end)) g)
in ((uu____1834), (bs)))
in (match (uu____1809) with
| (FStar_Pervasives_Native.None, []) -> begin
()
end
| (FStar_Pervasives_Native.Some (uu____1911, hd1, gamma_tail), (uu____1914)::uu____1915) -> begin
(

let uu____1974 = (FStar_Util.prefix bs)
in (match (uu____1974) with
| (uu____1999, (x, uu____2001)) -> begin
(match (hd1) with
| FStar_Syntax_Syntax.Binding_var (x') when (FStar_Syntax_Syntax.bv_eq x x') -> begin
()
end
| uu____2029 -> begin
(fail1 ())
end)
end))
end
| uu____2030 -> begin
(fail1 ())
end))
end))))




