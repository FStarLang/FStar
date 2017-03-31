
open Prims
type rel =
| EQ
| SUB
| SUBINV


let uu___is_EQ : rel  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EQ -> begin
true
end
| uu____4 -> begin
false
end))


let uu___is_SUB : rel  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SUB -> begin
true
end
| uu____8 -> begin
false
end))


let uu___is_SUBINV : rel  ->  Prims.bool = (fun projectee -> (match (projectee) with
| SUBINV -> begin
true
end
| uu____12 -> begin
false
end))

type ('a, 'b) problem =
{pid : Prims.int; lhs : 'a; relation : rel; rhs : 'a; element : 'b Prims.option; logical_guard : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term); scope : FStar_Syntax_Syntax.binders; reason : Prims.string Prims.list; loc : FStar_Range.range; rank : Prims.int Prims.option}

type prob =
| TProb of (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) problem
| CProb of (FStar_Syntax_Syntax.comp, Prims.unit) problem


let uu___is_TProb : prob  ->  Prims.bool = (fun projectee -> (match (projectee) with
| TProb (_0) -> begin
true
end
| uu____240 -> begin
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
| uu____260 -> begin
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
| uu____281 -> begin
false
end))


let uu___is_NonTrivial : guard_formula  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonTrivial (_0) -> begin
true
end
| uu____286 -> begin
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


let tconst : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun l -> (

let uu____304 = (

let uu____307 = (

let uu____308 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None)
in FStar_Syntax_Syntax.Tm_fvar (uu____308))
in (FStar_Syntax_Syntax.mk uu____307))
in (uu____304 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) FStar_Range.dummyRange)))


let tabbrev : FStar_Ident.lident  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun l -> (

let uu____322 = (

let uu____325 = (

let uu____326 = (FStar_Syntax_Syntax.lid_as_fv l (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in FStar_Syntax_Syntax.Tm_fvar (uu____326))
in (FStar_Syntax_Syntax.mk uu____325))
in (uu____322 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) FStar_Range.dummyRange)))


let t_unit : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.unit_lid)


let t_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.bool_lid)


let t_int : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.int_lid)


let t_string : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.string_lid)


let t_float : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.float_lid)


let t_char : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tabbrev FStar_Syntax_Const.char_lid)


let t_range : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (tconst FStar_Syntax_Const.range_lid)


let t_tactic_unit : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (

let uu____351 = (

let uu____352 = (

let uu____353 = (tabbrev FStar_Syntax_Const.tactic_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____353 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____354 = (

let uu____355 = (FStar_Syntax_Syntax.as_arg t_unit)
in (uu____355)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____352 uu____354)))
in (uu____351 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) FStar_Range.dummyRange))


let unit_const : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit))) (Some (t_unit.FStar_Syntax_Syntax.n)) FStar_Range.dummyRange)


let mk_by_tactic : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun tac f -> (

let t_by_tactic = (

let uu____379 = (tabbrev FStar_Syntax_Const.by_tactic_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____379 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let tac1 = (

let uu____383 = (

let uu____384 = (tabbrev FStar_Syntax_Const.reify_tactic_lid)
in (

let uu____385 = (

let uu____386 = (FStar_Syntax_Syntax.as_arg tac)
in (uu____386)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____384 uu____385)))
in (uu____383 None FStar_Range.dummyRange))
in (

let uu____391 = (

let uu____392 = (

let uu____393 = (FStar_Syntax_Syntax.as_arg tac1)
in (

let uu____394 = (

let uu____396 = (FStar_Syntax_Syntax.as_arg f)
in (uu____396)::[])
in (uu____393)::uu____394))
in (FStar_Syntax_Syntax.mk_Tm_app t_by_tactic uu____392))
in (uu____391 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) FStar_Range.dummyRange)))))


let rec delta_depth_greater_than : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth  ->  Prims.bool = (fun l m -> (match (((l), (m))) with
| (FStar_Syntax_Syntax.Delta_constant, uu____407) -> begin
false
end
| (FStar_Syntax_Syntax.Delta_equational, uu____408) -> begin
true
end
| (uu____409, FStar_Syntax_Syntax.Delta_equational) -> begin
false
end
| (FStar_Syntax_Syntax.Delta_defined_at_level (i), FStar_Syntax_Syntax.Delta_defined_at_level (j)) -> begin
(i > j)
end
| (FStar_Syntax_Syntax.Delta_defined_at_level (uu____412), FStar_Syntax_Syntax.Delta_constant) -> begin
true
end
| (FStar_Syntax_Syntax.Delta_abstract (d), uu____414) -> begin
(delta_depth_greater_than d m)
end
| (uu____415, FStar_Syntax_Syntax.Delta_abstract (d)) -> begin
(delta_depth_greater_than l d)
end))


let rec decr_delta_depth : FStar_Syntax_Syntax.delta_depth  ->  FStar_Syntax_Syntax.delta_depth Prims.option = (fun uu___93_420 -> (match (uu___93_420) with
| (FStar_Syntax_Syntax.Delta_constant) | (FStar_Syntax_Syntax.Delta_equational) -> begin
None
end
| FStar_Syntax_Syntax.Delta_defined_at_level (_0_27) when (_0_27 = (Prims.parse_int "1")) -> begin
Some (FStar_Syntax_Syntax.Delta_constant)
end
| FStar_Syntax_Syntax.Delta_defined_at_level (i) -> begin
Some (FStar_Syntax_Syntax.Delta_defined_at_level ((i - (Prims.parse_int "1"))))
end
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(decr_delta_depth d)
end))

type identifier_info =
{identifier : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either; identifier_ty : FStar_Syntax_Syntax.typ}


let rec insert_col_info = (fun col info col_infos -> (match (col_infos) with
| [] -> begin
(((col), (info)))::[]
end
| ((c, i))::rest -> begin
(match ((col < c)) with
| true -> begin
(((col), (info)))::col_infos
end
| uu____489 -> begin
(

let uu____490 = (insert_col_info col info rest)
in (((c), (i)))::uu____490)
end)
end))


let find_nearest_preceding_col_info = (fun col col_infos -> (

let rec aux = (fun out uu___94_526 -> (match (uu___94_526) with
| [] -> begin
out
end
| ((c, i))::rest -> begin
(match ((c > col)) with
| true -> begin
out
end
| uu____543 -> begin
(aux (Some (i)) rest)
end)
end))
in (aux None col_infos)))


type col_info =
(Prims.int * identifier_info) Prims.list


type row_info =
col_info FStar_ST.ref FStar_Util.imap


type file_info =
row_info FStar_Util.smap


let mk_info : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.typ  ->  identifier_info = (fun id ty -> {identifier = id; identifier_ty = ty})


let file_info_table : row_info FStar_Util.smap = (FStar_Util.smap_create (Prims.parse_int "50"))


let insert_identifier_info : (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  Prims.unit = (fun id ty range -> (

let info = (mk_info id ty)
in (

let use_range = (

let uu___95_576 = range
in {FStar_Range.def_range = range.FStar_Range.use_range; FStar_Range.use_range = uu___95_576.FStar_Range.use_range})
in (

let fn = (FStar_Range.file_of_range use_range)
in (

let start = (FStar_Range.start_of_range use_range)
in (

let uu____579 = (

let uu____582 = (FStar_Range.line_of_pos start)
in (

let uu____583 = (FStar_Range.col_of_pos start)
in ((uu____582), (uu____583))))
in (match (uu____579) with
| (row, col) -> begin
(

let uu____586 = (FStar_Util.smap_try_find file_info_table fn)
in (match (uu____586) with
| None -> begin
(

let col_info = (

let uu____593 = (insert_col_info col info [])
in (FStar_Util.mk_ref uu____593))
in (

let rows = (FStar_Util.imap_create (Prims.parse_int "1000"))
in ((FStar_Util.imap_add rows row col_info);
(FStar_Util.smap_add file_info_table fn rows);
)))
end
| Some (file_rows) -> begin
(

let uu____621 = (FStar_Util.imap_try_find file_rows row)
in (match (uu____621) with
| None -> begin
(

let col_info = (

let uu____631 = (insert_col_info col info [])
in (FStar_Util.mk_ref uu____631))
in (FStar_Util.imap_add file_rows row col_info))
end
| Some (col_infos) -> begin
(

let uu____647 = (

let uu____648 = (FStar_ST.read col_infos)
in (insert_col_info col info uu____648))
in (FStar_ST.write col_infos uu____647))
end))
end))
end)))))))


let info_at_pos : Prims.string  ->  Prims.int  ->  Prims.int  ->  identifier_info Prims.option = (fun fn row col -> (

let uu____667 = (FStar_Util.smap_try_find file_info_table fn)
in (match (uu____667) with
| None -> begin
None
end
| Some (rows) -> begin
(

let uu____671 = (FStar_Util.imap_try_find rows row)
in (match (uu____671) with
| None -> begin
None
end
| Some (cols) -> begin
(

let uu____680 = (

let uu____682 = (FStar_ST.read cols)
in (find_nearest_preceding_col_info col uu____682))
in (match (uu____680) with
| None -> begin
None
end
| Some (ci) -> begin
Some (ci)
end))
end))
end)))


let insert_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun bv ty -> (

let uu____696 = (FStar_Syntax_Syntax.range_of_bv bv)
in (insert_identifier_info (FStar_Util.Inl (bv)) ty uu____696)))


let insert_fv : FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun fv ty -> (

let uu____703 = (FStar_Syntax_Syntax.range_of_fv fv)
in (insert_identifier_info (FStar_Util.Inr (fv)) ty uu____703)))




