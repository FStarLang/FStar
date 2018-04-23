
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

type 'a problem =
{pid : Prims.int; lhs : 'a; relation : rel; rhs : 'a; element : FStar_Syntax_Syntax.term FStar_Pervasives_Native.option; logical_guard : FStar_Syntax_Syntax.term; logical_guard_uvar : (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option * FStar_Syntax_Syntax.ctx_uvar); scope : FStar_Syntax_Syntax.binders; reason : Prims.string Prims.list; loc : FStar_Range.range; rank : Prims.int FStar_Pervasives_Native.option}


let __proj__Mkproblem__item__pid : 'a . 'a problem  ->  Prims.int = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__pid
end))


let __proj__Mkproblem__item__lhs : 'a . 'a problem  ->  'a = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__lhs
end))


let __proj__Mkproblem__item__relation : 'a . 'a problem  ->  rel = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__relation
end))


let __proj__Mkproblem__item__rhs : 'a . 'a problem  ->  'a = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__rhs
end))


let __proj__Mkproblem__item__element : 'a . 'a problem  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__element
end))


let __proj__Mkproblem__item__logical_guard : 'a . 'a problem  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__logical_guard
end))


let __proj__Mkproblem__item__logical_guard_uvar : 'a . 'a problem  ->  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option * FStar_Syntax_Syntax.ctx_uvar) = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__logical_guard_uvar
end))


let __proj__Mkproblem__item__scope : 'a . 'a problem  ->  FStar_Syntax_Syntax.binders = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__scope
end))


let __proj__Mkproblem__item__reason : 'a . 'a problem  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__reason
end))


let __proj__Mkproblem__item__loc : 'a . 'a problem  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__loc
end))


let __proj__Mkproblem__item__rank : 'a . 'a problem  ->  Prims.int FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__rank
end))

type prob =
| TProb of FStar_Syntax_Syntax.typ problem
| CProb of FStar_Syntax_Syntax.comp problem


let uu___is_TProb : prob  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TProb (_0) -> begin
true
end
| uu____531 -> begin
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
| uu____553 -> begin
false
end))


let __proj__CProb__item___0 : prob  ->  FStar_Syntax_Syntax.comp problem = (fun projectee -> (match (projectee) with
| CProb (_0) -> begin
_0
end))


let as_tprob : prob  ->  FStar_Syntax_Syntax.typ problem = (fun uu___55_573 -> (match (uu___55_573) with
| TProb (p) -> begin
p
end
| uu____579 -> begin
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
| uu____594 -> begin
false
end))


let uu___is_NonTrivial : guard_formula  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonTrivial (_0) -> begin
true
end
| uu____601 -> begin
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


let mk_by_tactic : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tac f -> (

let t_by_tactic = (

let uu____632 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____632 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let t_reify_tactic = (

let uu____634 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.reify_tactic_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____634 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let tac1 = (

let uu____638 = (

let uu____643 = (

let uu____644 = (FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit)
in (

let uu____651 = (

let uu____660 = (FStar_Syntax_Syntax.as_arg tac)
in (uu____660)::[])
in (uu____644)::uu____651))
in (FStar_Syntax_Syntax.mk_Tm_app t_reify_tactic uu____643))
in (uu____638 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let uu____687 = (

let uu____692 = (

let uu____693 = (FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit)
in (

let uu____700 = (

let uu____709 = (FStar_Syntax_Syntax.as_arg tac1)
in (

let uu____716 = (

let uu____725 = (FStar_Syntax_Syntax.as_arg f)
in (uu____725)::[])
in (uu____709)::uu____716))
in (uu____693)::uu____700))
in (FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____692))
in (uu____687 FStar_Pervasives_Native.None FStar_Range.dummyRange))))))


let rec delta_depth_greater_than : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth  ->  Prims.bool = (fun l m -> (match (((l), (m))) with
| (FStar_Syntax_Syntax.Delta_constant, uu____768) -> begin
false
end
| (FStar_Syntax_Syntax.Delta_equational, uu____769) -> begin
true
end
| (uu____770, FStar_Syntax_Syntax.Delta_equational) -> begin
false
end
| (FStar_Syntax_Syntax.Delta_defined_at_level (i), FStar_Syntax_Syntax.Delta_defined_at_level (j)) -> begin
(i > j)
end
| (FStar_Syntax_Syntax.Delta_defined_at_level (uu____773), FStar_Syntax_Syntax.Delta_constant) -> begin
true
end
| (FStar_Syntax_Syntax.Delta_abstract (d), uu____775) -> begin
(delta_depth_greater_than d m)
end
| (uu____776, FStar_Syntax_Syntax.Delta_abstract (d)) -> begin
(delta_depth_greater_than l d)
end))


let rec decr_delta_depth : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun uu___56_784 -> (match (uu___56_784) with
| FStar_Syntax_Syntax.Delta_constant -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Delta_equational -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Delta_defined_at_level (_0_16) when (_0_16 = (Prims.parse_int "1")) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Delta_defined_at_level (i) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_defined_at_level ((i - (Prims.parse_int "1"))))
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


let insert_col_info : 'Auu____860 . Prims.int  ->  'Auu____860  ->  (Prims.int * 'Auu____860) Prims.list  ->  (Prims.int * 'Auu____860) Prims.list = (fun col info col_infos -> (

let rec __insert = (fun aux rest -> (match (rest) with
| [] -> begin
((aux), ((((col), (info)))::[]))
end
| ((c, i))::rest' -> begin
(match ((col < c)) with
| true -> begin
((aux), ((((col), (info)))::rest))
end
| uu____1030 -> begin
(__insert ((((c), (i)))::aux) rest')
end)
end))
in (

let uu____1035 = (__insert [] col_infos)
in (match (uu____1035) with
| (l, r) -> begin
(FStar_List.append (FStar_List.rev l) r)
end))))


let find_nearest_preceding_col_info : 'Auu____1102 . Prims.int  ->  (Prims.int * 'Auu____1102) Prims.list  ->  'Auu____1102 FStar_Pervasives_Native.option = (fun col col_infos -> (

let rec aux = (fun out uu___57_1147 -> (match (uu___57_1147) with
| [] -> begin
out
end
| ((c, i))::rest -> begin
(match ((c > col)) with
| true -> begin
out
end
| uu____1177 -> begin
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

let uu____1239 = (FStar_Util.psmap_empty ())
in {id_info_enabled = false; id_info_db = uu____1239; id_info_buffer = []})


let id_info__insert : (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  (Prims.int * identifier_info) Prims.list FStar_Util.pimap FStar_Util.psmap  ->  identifier_info  ->  (Prims.int * identifier_info) Prims.list FStar_Util.pimap FStar_Util.psmap = (fun ty_map db info -> (

let range = info.identifier_range
in (

let use_range1 = (

let uu____1292 = (FStar_Range.use_range range)
in (FStar_Range.set_def_range range uu____1292))
in (

let info1 = (

let uu___60_1294 = info
in (

let uu____1295 = (ty_map info.identifier_ty)
in {identifier = uu___60_1294.identifier; identifier_ty = uu____1295; identifier_range = use_range1}))
in (

let fn = (FStar_Range.file_of_range use_range1)
in (

let start = (FStar_Range.start_of_range use_range1)
in (

let uu____1298 = (

let uu____1303 = (FStar_Range.line_of_pos start)
in (

let uu____1304 = (FStar_Range.col_of_pos start)
in ((uu____1303), (uu____1304))))
in (match (uu____1298) with
| (row, col) -> begin
(

let rows = (

let uu____1326 = (FStar_Util.pimap_empty ())
in (FStar_Util.psmap_find_default db fn uu____1326))
in (

let cols = (FStar_Util.pimap_find_default rows row [])
in (

let uu____1366 = (

let uu____1375 = (insert_col_info col info1 cols)
in (FStar_All.pipe_right uu____1375 (FStar_Util.pimap_add rows row)))
in (FStar_All.pipe_right uu____1366 (FStar_Util.psmap_add db fn)))))
end))))))))


let id_info_insert : id_info_table  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  id_info_table = (fun table id1 ty range -> (

let info = {identifier = id1; identifier_ty = ty; identifier_range = range}
in (

let uu___61_1457 = table
in {id_info_enabled = uu___61_1457.id_info_enabled; id_info_db = uu___61_1457.id_info_db; id_info_buffer = (info)::table.id_info_buffer})))


let id_info_insert_bv : id_info_table  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  id_info_table = (fun table bv ty -> (match (table.id_info_enabled) with
| true -> begin
(

let uu____1473 = (FStar_Syntax_Syntax.range_of_bv bv)
in (id_info_insert table (FStar_Util.Inl (bv)) ty uu____1473))
end
| uu____1474 -> begin
table
end))


let id_info_insert_fv : id_info_table  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  id_info_table = (fun table fv ty -> (match (table.id_info_enabled) with
| true -> begin
(

let uu____1490 = (FStar_Syntax_Syntax.range_of_fv fv)
in (id_info_insert table (FStar_Util.Inr (fv)) ty uu____1490))
end
| uu____1491 -> begin
table
end))


let id_info_toggle : id_info_table  ->  Prims.bool  ->  id_info_table = (fun table enabled -> (

let uu___62_1502 = table
in (

let uu____1503 = (enabled && (FStar_Options.ide ()))
in {id_info_enabled = uu____1503; id_info_db = uu___62_1502.id_info_db; id_info_buffer = uu___62_1502.id_info_buffer})))


let id_info_promote : id_info_table  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  id_info_table = (fun table ty_map -> (

let uu___63_1519 = table
in (

let uu____1520 = (FStar_List.fold_left (id_info__insert ty_map) table.id_info_db table.id_info_buffer)
in {id_info_enabled = uu___63_1519.id_info_enabled; id_info_db = uu____1520; id_info_buffer = []})))


let id_info_at_pos : id_info_table  ->  Prims.string  ->  Prims.int  ->  Prims.int  ->  identifier_info FStar_Pervasives_Native.option = (fun table fn row col -> (

let rows = (

let uu____1556 = (FStar_Util.pimap_empty ())
in (FStar_Util.psmap_find_default table.id_info_db fn uu____1556))
in (

let cols = (FStar_Util.pimap_find_default rows row [])
in (

let uu____1562 = (find_nearest_preceding_col_info col cols)
in (match (uu____1562) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (info) -> begin
(

let last_col = (

let uu____1569 = (FStar_Range.end_of_range info.identifier_range)
in (FStar_Range.col_of_pos uu____1569))
in (match ((col <= last_col)) with
| true -> begin
FStar_Pervasives_Native.Some (info)
end
| uu____1572 -> begin
FStar_Pervasives_Native.None
end))
end)))))


let check_uvar_ctx_invariant : Prims.string  ->  FStar_Range.range  ->  Prims.bool  ->  FStar_Syntax_Syntax.gamma  ->  FStar_Syntax_Syntax.binders  ->  unit = (fun reason r should_check g bs -> (

let print_gamma = (fun gamma -> (

let uu____1608 = (FStar_All.pipe_right gamma (FStar_List.map (fun uu___58_1618 -> (match (uu___58_1618) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let uu____1620 = (FStar_Syntax_Print.bv_to_string x)
in (Prims.strcat "Binding_var " uu____1620))
end
| FStar_Syntax_Syntax.Binding_univ (u) -> begin
(Prims.strcat "Binding_univ " u.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.Binding_lid (l, uu____1623) -> begin
(

let uu____1640 = (FStar_Ident.string_of_lid l)
in (Prims.strcat "Binding_lid " uu____1640))
end))))
in (FStar_All.pipe_right uu____1608 (FStar_String.concat "::\n"))))
in (

let fail1 = (fun uu____1648 -> (

let uu____1649 = (

let uu____1650 = (FStar_Range.string_of_range r)
in (

let uu____1651 = (print_gamma g)
in (

let uu____1652 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.format5 "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n" reason uu____1650 (match (should_check) with
| true -> begin
"true"
end
| uu____1653 -> begin
"false"
end) uu____1651 uu____1652))))
in (failwith uu____1649)))
in (match ((not (should_check))) with
| true -> begin
()
end
| uu____1654 -> begin
(

let uu____1655 = (

let uu____1678 = (FStar_Util.prefix_until (fun uu___59_1693 -> (match (uu___59_1693) with
| FStar_Syntax_Syntax.Binding_var (uu____1694) -> begin
true
end
| uu____1695 -> begin
false
end)) g)
in ((uu____1678), (bs)))
in (match (uu____1655) with
| (FStar_Pervasives_Native.None, []) -> begin
()
end
| (FStar_Pervasives_Native.Some (uu____1746, hd1, gamma_tail), (uu____1749)::uu____1750) -> begin
(

let uu____1801 = (FStar_Util.prefix bs)
in (match (uu____1801) with
| (uu____1820, (x, uu____1822)) -> begin
(match (hd1) with
| FStar_Syntax_Syntax.Binding_var (x') when (FStar_Syntax_Syntax.bv_eq x x') -> begin
()
end
| uu____1840 -> begin
(fail1 ())
end)
end))
end
| uu____1841 -> begin
(fail1 ())
end))
end))))




