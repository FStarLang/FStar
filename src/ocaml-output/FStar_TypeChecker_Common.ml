
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


let rec decr_delta_depth : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option = (fun uu___102_657 -> (match (uu___102_657) with
| FStar_Syntax_Syntax.Delta_constant -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Delta_equational -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Delta_defined_at_level (_0_38) when (_0_38 = (Prims.parse_int "1")) -> begin
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

let rec aux = (fun out uu___103_1001 -> (match (uu___103_1001) with
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


type col_info =
(Prims.int * identifier_info) Prims.list


type row_info =
col_info FStar_ST.ref FStar_Util.imap


type file_info =
row_info FStar_Util.smap


let mk_info : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  identifier_info = (fun id ty range -> {identifier = id; identifier_ty = ty; identifier_range = range})


let file_info_table : row_info FStar_Util.smap = (FStar_Util.smap_create (Prims.parse_int "50"))


let insert_identifier_info : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  (Prims.string * Prims.int * Prims.int) = (fun id ty range -> (

let use_range = (

let uu___104_1093 = range
in {FStar_Range.def_range = range.FStar_Range.use_range; FStar_Range.use_range = uu___104_1093.FStar_Range.use_range})
in (

let info = (mk_info id ty use_range)
in (

let fn = (FStar_Range.file_of_range use_range)
in (

let start = (FStar_Range.start_of_range use_range)
in (

let uu____1097 = (

let uu____1102 = (FStar_Range.line_of_pos start)
in (

let uu____1103 = (FStar_Range.col_of_pos start)
in ((uu____1102), (uu____1103))))
in (match (uu____1097) with
| (row, col) -> begin
((

let uu____1113 = (FStar_Util.smap_try_find file_info_table fn)
in (match (uu____1113) with
| FStar_Pervasives_Native.None -> begin
(

let col_info = (

let uu____1125 = (insert_col_info col info [])
in (FStar_Util.mk_ref uu____1125))
in (

let rows = (FStar_Util.imap_create (Prims.parse_int "1000"))
in ((FStar_Util.imap_add rows row col_info);
(FStar_Util.smap_add file_info_table fn rows);
)))
end
| FStar_Pervasives_Native.Some (file_rows) -> begin
(

let uu____1173 = (FStar_Util.imap_try_find file_rows row)
in (match (uu____1173) with
| FStar_Pervasives_Native.None -> begin
(

let col_info = (

let uu____1191 = (insert_col_info col info [])
in (FStar_Util.mk_ref uu____1191))
in (FStar_Util.imap_add file_rows row col_info))
end
| FStar_Pervasives_Native.Some (col_infos) -> begin
(

let uu____1217 = (

let uu____1218 = (FStar_ST.read col_infos)
in (insert_col_info col info uu____1218))
in (FStar_ST.write col_infos uu____1217))
end))
end));
((fn), (row), (col));
)
end)))))))


let info_at_pos : Prims.string  ->  Prims.int  ->  Prims.int  ->  identifier_info FStar_Pervasives_Native.option = (fun fn row col -> (

let uu____1245 = (FStar_Util.smap_try_find file_info_table fn)
in (match (uu____1245) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (rows) -> begin
(

let uu____1251 = (FStar_Util.imap_try_find rows row)
in (match (uu____1251) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (cols) -> begin
(

let uu____1267 = (

let uu____1270 = (FStar_ST.read cols)
in (find_nearest_preceding_col_info col uu____1270))
in (match (uu____1267) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (ci) -> begin
(

let last_col = (

let uu____1283 = (FStar_Range.end_of_range ci.identifier_range)
in (FStar_Range.col_of_pos uu____1283))
in (match ((col <= last_col)) with
| true -> begin
FStar_Pervasives_Native.Some (ci)
end
| uu____1286 -> begin
FStar_Pervasives_Native.None
end))
end))
end))
end)))

type insert_id_info_ops =
{enable : Prims.bool  ->  Prims.unit; bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; fv : FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; promote : (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  Prims.unit}


let __proj__Mkinsert_id_info_ops__item__enable : insert_id_info_ops  ->  Prims.bool  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {enable = __fname__enable; bv = __fname__bv; fv = __fname__fv; promote = __fname__promote} -> begin
__fname__enable
end))


let __proj__Mkinsert_id_info_ops__item__bv : insert_id_info_ops  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {enable = __fname__enable; bv = __fname__bv; fv = __fname__fv; promote = __fname__promote} -> begin
__fname__bv
end))


let __proj__Mkinsert_id_info_ops__item__fv : insert_id_info_ops  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {enable = __fname__enable; bv = __fname__bv; fv = __fname__fv; promote = __fname__promote} -> begin
__fname__fv
end))


let __proj__Mkinsert_id_info_ops__item__promote : insert_id_info_ops  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {enable = __fname__enable; bv = __fname__bv; fv = __fname__fv; promote = __fname__promote} -> begin
__fname__promote
end))


let insert_id_info : insert_id_info_ops = (

let enabled = (FStar_Util.mk_ref false)
in (

let id_info_buffer = (FStar_Util.mk_ref [])
in (

let enable = (fun b -> (

let uu____1504 = ((FStar_Options.ide ()) && b)
in (FStar_ST.write enabled uu____1504)))
in (

let bv = (fun x t -> (

let uu____1514 = (FStar_ST.read enabled)
in (match (uu____1514) with
| true -> begin
(

let uu____1517 = (

let uu____1530 = (

let uu____1541 = (FStar_Syntax_Syntax.range_of_bv x)
in ((FStar_Util.Inl (x)), (t), (uu____1541)))
in (

let uu____1546 = (FStar_ST.read id_info_buffer)
in (uu____1530)::uu____1546))
in (FStar_ST.write id_info_buffer uu____1517))
end
| uu____1597 -> begin
()
end)))
in (

let fv = (fun x t -> (

let uu____1605 = (FStar_ST.read enabled)
in (match (uu____1605) with
| true -> begin
(

let uu____1608 = (

let uu____1621 = (

let uu____1632 = (FStar_Syntax_Syntax.range_of_fv x)
in ((FStar_Util.Inr (x)), (t), (uu____1632)))
in (

let uu____1637 = (FStar_ST.read id_info_buffer)
in (uu____1621)::uu____1637))
in (FStar_ST.write id_info_buffer uu____1608))
end
| uu____1688 -> begin
()
end)))
in (

let promote = (fun cb -> ((

let uu____1699 = (FStar_ST.read id_info_buffer)
in (FStar_All.pipe_right uu____1699 (FStar_List.iter (fun uu____1753 -> (match (uu____1753) with
| (i, t, r) -> begin
(

let uu____1775 = (

let uu____1782 = (cb t)
in (insert_identifier_info i uu____1782 r))
in (FStar_All.pipe_left FStar_Pervasives.ignore uu____1775))
end)))));
(FStar_ST.write id_info_buffer []);
))
in {enable = enable; bv = bv; fv = fv; promote = promote}))))))




