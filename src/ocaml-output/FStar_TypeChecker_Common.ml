
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
| uu____5 -> begin
false
end))


let uu___is_SUB : rel  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SUB -> begin
true
end
| uu____10 -> begin
false
end))


let uu___is_SUBINV : rel  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SUBINV -> begin
true
end
| uu____15 -> begin
false
end))

type ('a, 'b) problem =
{pid : Prims.int; lhs : 'a; relation : rel; rhs : 'a; element : 'b FStar_Pervasives_Native.option; logical_guard : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term); scope : FStar_Syntax_Syntax.binders; reason : Prims.string Prims.list; loc : FStar_Range.range; rank : Prims.int FStar_Pervasives_Native.option}


let __proj__Mkproblem__item__pid : 'a 'b . ('a, 'b) problem  ->  Prims.int = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__pid
end))


let __proj__Mkproblem__item__lhs : 'a 'b . ('a, 'b) problem  ->  'a = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__lhs
end))


let __proj__Mkproblem__item__relation : 'a 'b . ('a, 'b) problem  ->  rel = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__relation
end))


let __proj__Mkproblem__item__rhs : 'a 'b . ('a, 'b) problem  ->  'a = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__rhs
end))


let __proj__Mkproblem__item__element : 'a 'b . ('a, 'b) problem  ->  'b FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__element
end))


let __proj__Mkproblem__item__logical_guard : 'a 'b . ('a, 'b) problem  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__logical_guard
end))


let __proj__Mkproblem__item__scope : 'a 'b . ('a, 'b) problem  ->  FStar_Syntax_Syntax.binders = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__scope
end))


let __proj__Mkproblem__item__reason : 'a 'b . ('a, 'b) problem  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__reason
end))


let __proj__Mkproblem__item__loc : 'a 'b . ('a, 'b) problem  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__loc
end))


let __proj__Mkproblem__item__rank : 'a 'b . ('a, 'b) problem  ->  Prims.int FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; scope = __fname__scope; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__rank
end))

type prob =
| TProb of (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) problem
| CProb of (FStar_Syntax_Syntax.comp, Prims.unit) problem


let uu___is_TProb : prob  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TProb (_0) -> begin
true
end
| uu____509 -> begin
false
end))


let __proj__TProb__item___0 : prob  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) problem = (fun projectee -> (match (projectee) with
| TProb (_0) -> begin
_0
end))


let uu___is_CProb : prob  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CProb (_0) -> begin
true
end
| uu____539 -> begin
false
end))


let __proj__CProb__item___0 : prob  ->  (FStar_Syntax_Syntax.comp, Prims.unit) problem = (fun projectee -> (match (projectee) with
| CProb (_0) -> begin
_0
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
| uu____570 -> begin
false
end))


let uu___is_NonTrivial : guard_formula  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonTrivial (_0) -> begin
true
end
| uu____576 -> begin
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

let uu____606 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____606 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let t_reify_tactic = (

let uu____608 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.reify_tactic_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____608 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let tac1 = (

let uu____612 = (

let uu____613 = (

let uu____614 = (FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit)
in (

let uu____615 = (

let uu____618 = (FStar_Syntax_Syntax.as_arg tac)
in (uu____618)::[])
in (uu____614)::uu____615))
in (FStar_Syntax_Syntax.mk_Tm_app t_reify_tactic uu____613))
in (uu____612 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let uu____621 = (

let uu____622 = (

let uu____623 = (FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit)
in (

let uu____624 = (

let uu____627 = (FStar_Syntax_Syntax.as_arg tac1)
in (

let uu____628 = (

let uu____631 = (FStar_Syntax_Syntax.as_arg f)
in (uu____631)::[])
in (uu____627)::uu____628))
in (uu____623)::uu____624))
in (FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____622))
in (uu____621 FStar_Pervasives_Native.None FStar_Range.dummyRange))))))


let rec delta_depth_greater_than : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth  ->  Prims.bool = (fun l m -> (match (((l), (m))) with
| (FStar_Syntax_Syntax.Delta_constant, uu____642) -> begin
false
end
| (FStar_Syntax_Syntax.Delta_equational, uu____643) -> begin
true
end
| (uu____644, FStar_Syntax_Syntax.Delta_equational) -> begin
false
end
| (FStar_Syntax_Syntax.Delta_defined_at_level (i), FStar_Syntax_Syntax.Delta_defined_at_level (j)) -> begin
(i > j)
end
| (FStar_Syntax_Syntax.Delta_defined_at_level (uu____647), FStar_Syntax_Syntax.Delta_constant) -> begin
true
end
| (FStar_Syntax_Syntax.Delta_abstract (d), uu____649) -> begin
(delta_depth_greater_than d m)
end
| (uu____650, FStar_Syntax_Syntax.Delta_abstract (d)) -> begin
(delta_depth_greater_than l d)
end))


let rec decr_delta_depth : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun uu___104_657 -> (match (uu___104_657) with
| FStar_Syntax_Syntax.Delta_constant -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Delta_equational -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Delta_defined_at_level (_0_40) when (_0_40 = (Prims.parse_int "1")) -> begin
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


let insert_col_info : 'Auu____727 . Prims.int  ->  'Auu____727  ->  (Prims.int * 'Auu____727) Prims.list  ->  (Prims.int * 'Auu____727) Prims.list = (fun col info col_infos -> (

let rec __insert = (fun aux rest -> (match (rest) with
| [] -> begin
((aux), ((((col), (info)))::[]))
end
| ((c, i))::rest' -> begin
(match ((col < c)) with
| true -> begin
((aux), ((((col), (info)))::rest))
end
| uu____890 -> begin
(__insert ((((c), (i)))::aux) rest')
end)
end))
in (

let uu____895 = (__insert [] col_infos)
in (match (uu____895) with
| (l, r) -> begin
(FStar_List.append (FStar_List.rev l) r)
end))))


let find_nearest_preceding_col_info : 'Auu____962 . Prims.int  ->  (Prims.int * 'Auu____962) Prims.list  ->  'Auu____962 FStar_Pervasives_Native.option = (fun col col_infos -> (

let rec aux = (fun out uu___105_1001 -> (match (uu___105_1001) with
| [] -> begin
out
end
| ((c, i))::rest -> begin
(match ((c > col)) with
| true -> begin
out
end
| uu____1031 -> begin
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

let uu____1087 = (FStar_Util.psmap_empty ())
in {id_info_enabled = false; id_info_db = uu____1087; id_info_buffer = []})


let id_info__insert : (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  (Prims.int * identifier_info) Prims.list FStar_Util.pimap FStar_Util.psmap  ->  identifier_info  ->  (Prims.int * identifier_info) Prims.list FStar_Util.pimap FStar_Util.psmap = (fun ty_map db info -> (

let range = info.identifier_range
in (

let use_range = (

let uu___106_1137 = range
in {FStar_Range.def_range = range.FStar_Range.use_range; FStar_Range.use_range = uu___106_1137.FStar_Range.use_range})
in (

let info1 = (

let uu___107_1139 = info
in (

let uu____1140 = (ty_map info.identifier_ty)
in {identifier = uu___107_1139.identifier; identifier_ty = uu____1140; identifier_range = use_range}))
in (

let fn = (FStar_Range.file_of_range use_range)
in (

let start = (FStar_Range.start_of_range use_range)
in (

let uu____1143 = (

let uu____1148 = (FStar_Range.line_of_pos start)
in (

let uu____1149 = (FStar_Range.col_of_pos start)
in ((uu____1148), (uu____1149))))
in (match (uu____1143) with
| (row, col) -> begin
(

let rows = (

let uu____1171 = (FStar_Util.pimap_empty ())
in (FStar_Util.psmap_find_default db fn uu____1171))
in (

let cols = (FStar_Util.pimap_find_default rows row [])
in (

let uu____1211 = (

let uu____1220 = (insert_col_info col info1 cols)
in (FStar_All.pipe_right uu____1220 (FStar_Util.pimap_add rows row)))
in (FStar_All.pipe_right uu____1211 (FStar_Util.psmap_add db fn)))))
end))))))))


let id_info_insert : id_info_table  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  id_info_table = (fun table id ty range -> (

let info = {identifier = id; identifier_ty = ty; identifier_range = range}
in (

let uu___108_1298 = table
in {id_info_enabled = uu___108_1298.id_info_enabled; id_info_db = uu___108_1298.id_info_db; id_info_buffer = (info)::table.id_info_buffer})))


let id_info_insert_bv : id_info_table  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  id_info_table = (fun table bv ty -> (match (table.id_info_enabled) with
| true -> begin
(

let uu____1311 = (FStar_Syntax_Syntax.range_of_bv bv)
in (id_info_insert table (FStar_Util.Inl (bv)) ty uu____1311))
end
| uu____1312 -> begin
table
end))


let id_info_insert_fv : id_info_table  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  id_info_table = (fun table fv ty -> (match (table.id_info_enabled) with
| true -> begin
(

let uu____1325 = (FStar_Syntax_Syntax.range_of_fv fv)
in (id_info_insert table (FStar_Util.Inr (fv)) ty uu____1325))
end
| uu____1326 -> begin
table
end))


let id_info_toggle : id_info_table  ->  Prims.bool  ->  id_info_table = (fun table enabled -> (

let uu___109_1335 = table
in (

let uu____1336 = (enabled && (FStar_Options.ide ()))
in {id_info_enabled = uu____1336; id_info_db = uu___109_1335.id_info_db; id_info_buffer = uu___109_1335.id_info_buffer})))


let id_info_promote : id_info_table  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  id_info_table = (fun table ty_map -> (

let uu___110_1350 = table
in (

let uu____1351 = (FStar_List.fold_left (id_info__insert ty_map) table.id_info_db table.id_info_buffer)
in {id_info_enabled = uu___110_1350.id_info_enabled; id_info_db = uu____1351; id_info_buffer = []})))


let id_info_at_pos : id_info_table  ->  Prims.string  ->  Prims.int  ->  Prims.int  ->  identifier_info FStar_Pervasives_Native.option = (fun table fn row col -> (

let rows = (

let uu____1383 = (FStar_Util.pimap_empty ())
in (FStar_Util.psmap_find_default table.id_info_db fn uu____1383))
in (

let cols = (FStar_Util.pimap_find_default rows row [])
in (

let uu____1389 = (find_nearest_preceding_col_info col cols)
in (match (uu____1389) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (info) -> begin
(

let last_col = (

let uu____1396 = (FStar_Range.end_of_range info.identifier_range)
in (FStar_Range.col_of_pos uu____1396))
in (match ((col <= last_col)) with
| true -> begin
FStar_Pervasives_Native.Some (info)
end
| uu____1399 -> begin
FStar_Pervasives_Native.None
end))
end)))))




