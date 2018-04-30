
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
{pid : Prims.int; lhs : 'a; relation : rel; rhs : 'a; element : FStar_Syntax_Syntax.term FStar_Pervasives_Native.option; logical_guard : FStar_Syntax_Syntax.term; logical_guard_uvar : (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.ctx_uvar); reason : Prims.string Prims.list; loc : FStar_Range.range; rank : rank_t FStar_Pervasives_Native.option}


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


let __proj__Mkproblem__item__element : 'a . 'a problem  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__element
end))


let __proj__Mkproblem__item__logical_guard : 'a . 'a problem  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {pid = __fname__pid; lhs = __fname__lhs; relation = __fname__relation; rhs = __fname__rhs; element = __fname__element; logical_guard = __fname__logical_guard; logical_guard_uvar = __fname__logical_guard_uvar; reason = __fname__reason; loc = __fname__loc; rank = __fname__rank} -> begin
__fname__logical_guard
end))


let __proj__Mkproblem__item__logical_guard_uvar : 'a . 'a problem  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.ctx_uvar) = (fun projectee -> (match (projectee) with
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
| uu____491 -> begin
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
| uu____513 -> begin
false
end))


let __proj__CProb__item___0 : prob  ->  FStar_Syntax_Syntax.comp problem = (fun projectee -> (match (projectee) with
| CProb (_0) -> begin
_0
end))


let as_tprob : prob  ->  FStar_Syntax_Syntax.typ problem = (fun uu___55_533 -> (match (uu___55_533) with
| TProb (p) -> begin
p
end
| uu____539 -> begin
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
| uu____554 -> begin
false
end))


let uu___is_NonTrivial : guard_formula  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonTrivial (_0) -> begin
true
end
| uu____561 -> begin
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

let uu____592 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.by_tactic_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____592 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let t_reify_tactic = (

let uu____594 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.reify_tactic_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____594 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let tac1 = (

let uu____598 = (

let uu____603 = (

let uu____604 = (FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit)
in (

let uu____611 = (

let uu____620 = (FStar_Syntax_Syntax.as_arg tac)
in (uu____620)::[])
in (uu____604)::uu____611))
in (FStar_Syntax_Syntax.mk_Tm_app t_reify_tactic uu____603))
in (uu____598 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let uu____647 = (

let uu____652 = (

let uu____653 = (FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.t_unit)
in (

let uu____660 = (

let uu____669 = (FStar_Syntax_Syntax.as_arg tac1)
in (

let uu____676 = (

let uu____685 = (FStar_Syntax_Syntax.as_arg f)
in (uu____685)::[])
in (uu____669)::uu____676))
in (uu____653)::uu____660))
in (FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____652))
in (uu____647 FStar_Pervasives_Native.None FStar_Range.dummyRange))))))


let rec delta_depth_greater_than : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth  ->  Prims.bool = (fun l m -> (match (((l), (m))) with
| (FStar_Syntax_Syntax.Delta_constant, uu____728) -> begin
false
end
| (FStar_Syntax_Syntax.Delta_equational, uu____729) -> begin
true
end
| (uu____730, FStar_Syntax_Syntax.Delta_equational) -> begin
false
end
| (FStar_Syntax_Syntax.Delta_defined_at_level (i), FStar_Syntax_Syntax.Delta_defined_at_level (j)) -> begin
(i > j)
end
| (FStar_Syntax_Syntax.Delta_defined_at_level (uu____733), FStar_Syntax_Syntax.Delta_constant) -> begin
true
end
| (FStar_Syntax_Syntax.Delta_abstract (d), uu____735) -> begin
(delta_depth_greater_than d m)
end
| (uu____736, FStar_Syntax_Syntax.Delta_abstract (d)) -> begin
(delta_depth_greater_than l d)
end))


let rec decr_delta_depth : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun uu___56_744 -> (match (uu___56_744) with
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


let insert_col_info : 'Auu____820 . Prims.int  ->  'Auu____820  ->  (Prims.int * 'Auu____820) Prims.list  ->  (Prims.int * 'Auu____820) Prims.list = (fun col info col_infos -> (

let rec __insert = (fun aux rest -> (match (rest) with
| [] -> begin
((aux), ((((col), (info)))::[]))
end
| ((c, i))::rest' -> begin
(match ((col < c)) with
| true -> begin
((aux), ((((col), (info)))::rest))
end
| uu____990 -> begin
(__insert ((((c), (i)))::aux) rest')
end)
end))
in (

let uu____995 = (__insert [] col_infos)
in (match (uu____995) with
| (l, r) -> begin
(FStar_List.append (FStar_List.rev l) r)
end))))


let find_nearest_preceding_col_info : 'Auu____1062 . Prims.int  ->  (Prims.int * 'Auu____1062) Prims.list  ->  'Auu____1062 FStar_Pervasives_Native.option = (fun col col_infos -> (

let rec aux = (fun out uu___57_1107 -> (match (uu___57_1107) with
| [] -> begin
out
end
| ((c, i))::rest -> begin
(match ((c > col)) with
| true -> begin
out
end
| uu____1137 -> begin
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

let uu____1199 = (FStar_Util.psmap_empty ())
in {id_info_enabled = false; id_info_db = uu____1199; id_info_buffer = []})


let id_info__insert : (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  (Prims.int * identifier_info) Prims.list FStar_Util.pimap FStar_Util.psmap  ->  identifier_info  ->  (Prims.int * identifier_info) Prims.list FStar_Util.pimap FStar_Util.psmap = (fun ty_map db info -> (

let range = info.identifier_range
in (

let use_range1 = (

let uu____1252 = (FStar_Range.use_range range)
in (FStar_Range.set_def_range range uu____1252))
in (

let info1 = (

let uu___60_1254 = info
in (

let uu____1255 = (ty_map info.identifier_ty)
in {identifier = uu___60_1254.identifier; identifier_ty = uu____1255; identifier_range = use_range1}))
in (

let fn = (FStar_Range.file_of_range use_range1)
in (

let start = (FStar_Range.start_of_range use_range1)
in (

let uu____1258 = (

let uu____1263 = (FStar_Range.line_of_pos start)
in (

let uu____1264 = (FStar_Range.col_of_pos start)
in ((uu____1263), (uu____1264))))
in (match (uu____1258) with
| (row, col) -> begin
(

let rows = (

let uu____1286 = (FStar_Util.pimap_empty ())
in (FStar_Util.psmap_find_default db fn uu____1286))
in (

let cols = (FStar_Util.pimap_find_default rows row [])
in (

let uu____1326 = (

let uu____1335 = (insert_col_info col info1 cols)
in (FStar_All.pipe_right uu____1335 (FStar_Util.pimap_add rows row)))
in (FStar_All.pipe_right uu____1326 (FStar_Util.psmap_add db fn)))))
end))))))))


let id_info_insert : id_info_table  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  id_info_table = (fun table id1 ty range -> (

let info = {identifier = id1; identifier_ty = ty; identifier_range = range}
in (

let uu___61_1417 = table
in {id_info_enabled = uu___61_1417.id_info_enabled; id_info_db = uu___61_1417.id_info_db; id_info_buffer = (info)::table.id_info_buffer})))


let id_info_insert_bv : id_info_table  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  id_info_table = (fun table bv ty -> (match (table.id_info_enabled) with
| true -> begin
(

let uu____1433 = (FStar_Syntax_Syntax.range_of_bv bv)
in (id_info_insert table (FStar_Util.Inl (bv)) ty uu____1433))
end
| uu____1434 -> begin
table
end))


let id_info_insert_fv : id_info_table  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  id_info_table = (fun table fv ty -> (match (table.id_info_enabled) with
| true -> begin
(

let uu____1450 = (FStar_Syntax_Syntax.range_of_fv fv)
in (id_info_insert table (FStar_Util.Inr (fv)) ty uu____1450))
end
| uu____1451 -> begin
table
end))


let id_info_toggle : id_info_table  ->  Prims.bool  ->  id_info_table = (fun table enabled -> (

let uu___62_1462 = table
in (

let uu____1463 = (enabled && (FStar_Options.ide ()))
in {id_info_enabled = uu____1463; id_info_db = uu___62_1462.id_info_db; id_info_buffer = uu___62_1462.id_info_buffer})))


let id_info_promote : id_info_table  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  id_info_table = (fun table ty_map -> (

let uu___63_1479 = table
in (

let uu____1480 = (FStar_List.fold_left (id_info__insert ty_map) table.id_info_db table.id_info_buffer)
in {id_info_enabled = uu___63_1479.id_info_enabled; id_info_db = uu____1480; id_info_buffer = []})))


let id_info_at_pos : id_info_table  ->  Prims.string  ->  Prims.int  ->  Prims.int  ->  identifier_info FStar_Pervasives_Native.option = (fun table fn row col -> (

let rows = (

let uu____1516 = (FStar_Util.pimap_empty ())
in (FStar_Util.psmap_find_default table.id_info_db fn uu____1516))
in (

let cols = (FStar_Util.pimap_find_default rows row [])
in (

let uu____1522 = (find_nearest_preceding_col_info col cols)
in (match (uu____1522) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (info) -> begin
(

let last_col = (

let uu____1529 = (FStar_Range.end_of_range info.identifier_range)
in (FStar_Range.col_of_pos uu____1529))
in (match ((col <= last_col)) with
| true -> begin
FStar_Pervasives_Native.Some (info)
end
| uu____1532 -> begin
FStar_Pervasives_Native.None
end))
end)))))


let check_uvar_ctx_invariant : Prims.string  ->  FStar_Range.range  ->  Prims.bool  ->  FStar_Syntax_Syntax.gamma  ->  FStar_Syntax_Syntax.binders  ->  unit = (fun reason r should_check g bs -> (

let print_gamma = (fun gamma -> (

let uu____1568 = (FStar_All.pipe_right gamma (FStar_List.map (fun uu___58_1578 -> (match (uu___58_1578) with
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let uu____1580 = (FStar_Syntax_Print.bv_to_string x)
in (Prims.strcat "Binding_var " uu____1580))
end
| FStar_Syntax_Syntax.Binding_univ (u) -> begin
(Prims.strcat "Binding_univ " u.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.Binding_lid (l, uu____1583) -> begin
(

let uu____1600 = (FStar_Ident.string_of_lid l)
in (Prims.strcat "Binding_lid " uu____1600))
end))))
in (FStar_All.pipe_right uu____1568 (FStar_String.concat "::\n"))))
in (

let fail1 = (fun uu____1608 -> (

let uu____1609 = (

let uu____1610 = (FStar_Range.string_of_range r)
in (

let uu____1611 = (print_gamma g)
in (

let uu____1612 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.format5 "Invariant violation: gamma and binders are out of sync\n\treason=%s, range=%s, should_check=%s\n\t\n                               gamma=%s\n\tbinders=%s\n" reason uu____1610 (match (should_check) with
| true -> begin
"true"
end
| uu____1613 -> begin
"false"
end) uu____1611 uu____1612))))
in (failwith uu____1609)))
in (match ((not (should_check))) with
| true -> begin
()
end
| uu____1614 -> begin
(

let uu____1615 = (

let uu____1638 = (FStar_Util.prefix_until (fun uu___59_1653 -> (match (uu___59_1653) with
| FStar_Syntax_Syntax.Binding_var (uu____1654) -> begin
true
end
| uu____1655 -> begin
false
end)) g)
in ((uu____1638), (bs)))
in (match (uu____1615) with
| (FStar_Pervasives_Native.None, []) -> begin
()
end
| (FStar_Pervasives_Native.Some (uu____1706, hd1, gamma_tail), (uu____1709)::uu____1710) -> begin
(

let uu____1761 = (FStar_Util.prefix bs)
in (match (uu____1761) with
| (uu____1780, (x, uu____1782)) -> begin
(match (hd1) with
| FStar_Syntax_Syntax.Binding_var (x') when (FStar_Syntax_Syntax.bv_eq x x') -> begin
()
end
| uu____1800 -> begin
(fail1 ())
end)
end))
end
| uu____1801 -> begin
(fail1 ())
end))
end))))




