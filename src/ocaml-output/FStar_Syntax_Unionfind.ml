
open Prims
open FStar_Pervasives
type vops_t =
{next_major : unit  ->  FStar_Syntax_Syntax.version; next_minor : unit  ->  FStar_Syntax_Syntax.version}


let __proj__Mkvops_t__item__next_major : vops_t  ->  unit  ->  FStar_Syntax_Syntax.version = (fun projectee -> (match (projectee) with
| {next_major = next_major; next_minor = next_minor} -> begin
next_major
end))


let __proj__Mkvops_t__item__next_minor : vops_t  ->  unit  ->  FStar_Syntax_Syntax.version = (fun projectee -> (match (projectee) with
| {next_major = next_major; next_minor = next_minor} -> begin
next_minor
end))


let vops : vops_t = (

let major = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let minor = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let next_major = (fun uu____85 -> ((FStar_ST.op_Colon_Equals minor (Prims.parse_int "0"));
(

let uu____109 = ((FStar_Util.incr major);
(FStar_ST.op_Bang major);
)
in {FStar_Syntax_Syntax.major = uu____109; FStar_Syntax_Syntax.minor = (Prims.parse_int "0")});
))
in (

let next_minor = (fun uu____139 -> (

let uu____140 = (FStar_ST.op_Bang major)
in (

let uu____163 = ((FStar_Util.incr minor);
(FStar_ST.op_Bang minor);
)
in {FStar_Syntax_Syntax.major = uu____140; FStar_Syntax_Syntax.minor = uu____163})))
in {next_major = next_major; next_minor = next_minor}))))


type tgraph =
FStar_Syntax_Syntax.term FStar_Pervasives_Native.option FStar_Unionfind.puf


type ugraph =
FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option FStar_Unionfind.puf

type uf =
{term_graph : tgraph; univ_graph : ugraph; version : FStar_Syntax_Syntax.version}


let __proj__Mkuf__item__term_graph : uf  ->  tgraph = (fun projectee -> (match (projectee) with
| {term_graph = term_graph; univ_graph = univ_graph; version = version} -> begin
term_graph
end))


let __proj__Mkuf__item__univ_graph : uf  ->  ugraph = (fun projectee -> (match (projectee) with
| {term_graph = term_graph; univ_graph = univ_graph; version = version} -> begin
univ_graph
end))


let __proj__Mkuf__item__version : uf  ->  FStar_Syntax_Syntax.version = (fun projectee -> (match (projectee) with
| {term_graph = term_graph; univ_graph = univ_graph; version = version} -> begin
version
end))


let empty : FStar_Syntax_Syntax.version  ->  uf = (fun v1 -> (

let uu____243 = (FStar_Unionfind.puf_empty ())
in (

let uu____246 = (FStar_Unionfind.puf_empty ())
in {term_graph = uu____243; univ_graph = uu____246; version = v1})))


let version_to_string : FStar_Syntax_Syntax.version  ->  Prims.string = (fun v1 -> (

let uu____256 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major)
in (

let uu____258 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor)
in (FStar_Util.format2 "%s.%s" uu____256 uu____258))))


let state : uf FStar_ST.ref = (

let uu____264 = (

let uu____265 = (vops.next_major ())
in (empty uu____265))
in (FStar_Util.mk_ref uu____264))

type tx =
| TX of uf


let uu___is_TX : tx  ->  Prims.bool = (fun projectee -> true)


let __proj__TX__item___0 : tx  ->  uf = (fun projectee -> (match (projectee) with
| TX (_0) -> begin
_0
end))


let get : unit  ->  uf = (fun uu____291 -> (FStar_ST.op_Bang state))


let set : uf  ->  unit = (fun u -> (FStar_ST.op_Colon_Equals state u))


let reset : unit  ->  unit = (fun uu____341 -> (

let v1 = (vops.next_major ())
in (

let uu____343 = (empty v1)
in (set uu____343))))


let new_transaction : unit  ->  tx = (fun uu____349 -> (

let tx = (

let uu____351 = (get ())
in TX (uu____351))
in ((

let uu____353 = (

let uu___34_354 = (get ())
in (

let uu____355 = (vops.next_minor ())
in {term_graph = uu___34_354.term_graph; univ_graph = uu___34_354.univ_graph; version = uu____355}))
in (set uu____353));
tx;
)))


let commit : tx  ->  unit = (fun tx -> ())


let rollback : tx  ->  unit = (fun uu____367 -> (match (uu____367) with
| TX (uf) -> begin
(set uf)
end))


let update_in_tx : 'a . 'a FStar_ST.ref  ->  'a  ->  unit = (fun r x -> ())


let get_term_graph : unit  ->  tgraph = (fun uu____396 -> (

let uu____397 = (get ())
in uu____397.term_graph))


let get_version : unit  ->  FStar_Syntax_Syntax.version = (fun uu____403 -> (

let uu____404 = (get ())
in uu____404.version))


let set_term_graph : tgraph  ->  unit = (fun tg -> (

let uu____411 = (

let uu___47_412 = (get ())
in {term_graph = tg; univ_graph = uu___47_412.univ_graph; version = uu___47_412.version})
in (set uu____411)))


let chk_v : 'Auu____418 . ('Auu____418 * FStar_Syntax_Syntax.version)  ->  'Auu____418 = (fun uu____427 -> (match (uu____427) with
| (u, v1) -> begin
(

let expected = (get_version ())
in (match (((Prims.op_Equality v1.FStar_Syntax_Syntax.major expected.FStar_Syntax_Syntax.major) && (v1.FStar_Syntax_Syntax.minor <= expected.FStar_Syntax_Syntax.minor))) with
| true -> begin
u
end
| uu____437 -> begin
(

let uu____439 = (

let uu____441 = (version_to_string expected)
in (

let uu____443 = (version_to_string v1)
in (FStar_Util.format2 "Incompatible version for unification variable: current version is %s; got version %s" uu____441 uu____443)))
in (failwith uu____439))
end))
end))


let uvar_id : FStar_Syntax_Syntax.uvar  ->  Prims.int = (fun u -> (

let uu____453 = (get_term_graph ())
in (

let uu____458 = (chk_v u)
in (FStar_Unionfind.puf_id uu____453 uu____458))))


let from_id : Prims.int  ->  FStar_Syntax_Syntax.uvar = (fun n1 -> (

let uu____479 = (

let uu____486 = (get_term_graph ())
in (FStar_Unionfind.puf_fromid uu____486 n1))
in (

let uu____493 = (get_version ())
in ((uu____479), (uu____493)))))


let fresh : unit  ->  FStar_Syntax_Syntax.uvar = (fun uu____505 -> (

let uu____506 = (

let uu____513 = (get_term_graph ())
in (FStar_Unionfind.puf_fresh uu____513 FStar_Pervasives_Native.None))
in (

let uu____520 = (get_version ())
in ((uu____506), (uu____520)))))


let find : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun u -> (

let uu____535 = (get_term_graph ())
in (

let uu____540 = (chk_v u)
in (FStar_Unionfind.puf_find uu____535 uu____540))))


let change : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term  ->  unit = (fun u t -> (

let uu____564 = (

let uu____565 = (get_term_graph ())
in (

let uu____570 = (chk_v u)
in (FStar_Unionfind.puf_change uu____565 uu____570 (FStar_Pervasives_Native.Some (t)))))
in (set_term_graph uu____564)))


let equiv : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.uvar  ->  Prims.bool = (fun u v1 -> (

let uu____595 = (get_term_graph ())
in (

let uu____600 = (chk_v u)
in (

let uu____611 = (chk_v v1)
in (FStar_Unionfind.puf_equivalent uu____595 uu____600 uu____611)))))


let union : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.uvar  ->  unit = (fun u v1 -> (

let uu____635 = (

let uu____636 = (get_term_graph ())
in (

let uu____641 = (chk_v u)
in (

let uu____652 = (chk_v v1)
in (FStar_Unionfind.puf_union uu____636 uu____641 uu____652))))
in (set_term_graph uu____635)))


let get_univ_graph : unit  ->  ugraph = (fun uu____670 -> (

let uu____671 = (get ())
in uu____671.univ_graph))


let set_univ_graph : ugraph  ->  unit = (fun ug -> (

let uu____678 = (

let uu___66_679 = (get ())
in {term_graph = uu___66_679.term_graph; univ_graph = ug; version = uu___66_679.version})
in (set uu____678)))


let univ_uvar_id : FStar_Syntax_Syntax.universe_uvar  ->  Prims.int = (fun u -> (

let uu____687 = (get_univ_graph ())
in (

let uu____692 = (chk_v u)
in (FStar_Unionfind.puf_id uu____687 uu____692))))


let univ_from_id : Prims.int  ->  FStar_Syntax_Syntax.universe_uvar = (fun n1 -> (

let uu____711 = (

let uu____716 = (get_univ_graph ())
in (FStar_Unionfind.puf_fromid uu____716 n1))
in (

let uu____723 = (get_version ())
in ((uu____711), (uu____723)))))


let univ_fresh : unit  ->  FStar_Syntax_Syntax.universe_uvar = (fun uu____733 -> (

let uu____734 = (

let uu____739 = (get_univ_graph ())
in (FStar_Unionfind.puf_fresh uu____739 FStar_Pervasives_Native.None))
in (

let uu____746 = (get_version ())
in ((uu____734), (uu____746)))))


let univ_find : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun u -> (

let uu____759 = (get_univ_graph ())
in (

let uu____764 = (chk_v u)
in (FStar_Unionfind.puf_find uu____759 uu____764))))


let univ_change : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe  ->  unit = (fun u t -> (

let uu____786 = (

let uu____787 = (get_univ_graph ())
in (

let uu____792 = (chk_v u)
in (FStar_Unionfind.puf_change uu____787 uu____792 (FStar_Pervasives_Native.Some (t)))))
in (set_univ_graph uu____786)))


let univ_equiv : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool = (fun u v1 -> (

let uu____815 = (get_univ_graph ())
in (

let uu____820 = (chk_v u)
in (

let uu____829 = (chk_v v1)
in (FStar_Unionfind.puf_equivalent uu____815 uu____820 uu____829)))))


let univ_union : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  unit = (fun u v1 -> (

let uu____851 = (

let uu____852 = (get_univ_graph ())
in (

let uu____857 = (chk_v u)
in (

let uu____866 = (chk_v v1)
in (FStar_Unionfind.puf_union uu____852 uu____857 uu____866))))
in (set_univ_graph uu____851)))




