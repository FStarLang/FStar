
open Prims
open FStar_Pervasives
type vops_t =
{next_major : unit  ->  FStar_Syntax_Syntax.version; next_minor : unit  ->  FStar_Syntax_Syntax.version}


let __proj__Mkvops_t__item__next_major : vops_t  ->  unit  ->  FStar_Syntax_Syntax.version = (fun projectee -> (match (projectee) with
| {next_major = __fname__next_major; next_minor = __fname__next_minor} -> begin
__fname__next_major
end))


let __proj__Mkvops_t__item__next_minor : vops_t  ->  unit  ->  FStar_Syntax_Syntax.version = (fun projectee -> (match (projectee) with
| {next_major = __fname__next_major; next_minor = __fname__next_minor} -> begin
__fname__next_minor
end))


let vops : vops_t = (

let major = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let minor = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let next_major = (fun uu____72 -> ((FStar_ST.op_Colon_Equals minor (Prims.parse_int "0"));
(

let uu____115 = ((FStar_Util.incr major);
(FStar_ST.op_Bang major);
)
in {FStar_Syntax_Syntax.major = uu____115; FStar_Syntax_Syntax.minor = (Prims.parse_int "0")});
))
in (

let next_minor = (fun uu____196 -> (

let uu____197 = (FStar_ST.op_Bang major)
in (

let uu____239 = ((FStar_Util.incr minor);
(FStar_ST.op_Bang minor);
)
in {FStar_Syntax_Syntax.major = uu____197; FStar_Syntax_Syntax.minor = uu____239})))
in {next_major = next_major; next_minor = next_minor}))))


type tgraph =
FStar_Syntax_Syntax.term FStar_Pervasives_Native.option FStar_Unionfind.puf


type ugraph =
FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option FStar_Unionfind.puf

type uf =
{term_graph : tgraph; univ_graph : ugraph; version : FStar_Syntax_Syntax.version}


let __proj__Mkuf__item__term_graph : uf  ->  tgraph = (fun projectee -> (match (projectee) with
| {term_graph = __fname__term_graph; univ_graph = __fname__univ_graph; version = __fname__version} -> begin
__fname__term_graph
end))


let __proj__Mkuf__item__univ_graph : uf  ->  ugraph = (fun projectee -> (match (projectee) with
| {term_graph = __fname__term_graph; univ_graph = __fname__univ_graph; version = __fname__version} -> begin
__fname__univ_graph
end))


let __proj__Mkuf__item__version : uf  ->  FStar_Syntax_Syntax.version = (fun projectee -> (match (projectee) with
| {term_graph = __fname__term_graph; univ_graph = __fname__univ_graph; version = __fname__version} -> begin
__fname__version
end))


let empty : FStar_Syntax_Syntax.version  ->  uf = (fun v1 -> (

let uu____367 = (FStar_Unionfind.puf_empty ())
in (

let uu____370 = (FStar_Unionfind.puf_empty ())
in {term_graph = uu____367; univ_graph = uu____370; version = v1})))


let version_to_string : FStar_Syntax_Syntax.version  ->  Prims.string = (fun v1 -> (

let uu____378 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major)
in (

let uu____379 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor)
in (FStar_Util.format2 "%s.%s" uu____378 uu____379))))


let state : uf FStar_ST.ref = (

let uu____393 = (

let uu____394 = (vops.next_major ())
in (empty uu____394))
in (FStar_Util.mk_ref uu____393))

type tx =
| TX of uf


let uu___is_TX : tx  ->  Prims.bool = (fun projectee -> true)


let __proj__TX__item___0 : tx  ->  uf = (fun projectee -> (match (projectee) with
| TX (_0) -> begin
_0
end))


let get : unit  ->  uf = (fun uu____415 -> (FStar_ST.op_Bang state))


let set : uf  ->  unit = (fun u -> (FStar_ST.op_Colon_Equals state u))


let reset : unit  ->  unit = (fun uu____463 -> (

let v1 = (vops.next_major ())
in (

let uu____465 = (empty v1)
in (set uu____465))))


let new_transaction : unit  ->  tx = (fun uu____470 -> (

let tx = (

let uu____472 = (get ())
in TX (uu____472))
in ((

let uu____474 = (

let uu___82_475 = (get ())
in (

let uu____476 = (vops.next_minor ())
in {term_graph = uu___82_475.term_graph; univ_graph = uu___82_475.univ_graph; version = uu____476}))
in (set uu____474));
tx;
)))


let commit : tx  ->  unit = (fun tx -> ())


let rollback : tx  ->  unit = (fun uu____486 -> (match (uu____486) with
| TX (uf) -> begin
(set uf)
end))


let update_in_tx : 'a . 'a FStar_ST.ref  ->  'a  ->  unit = (fun r x -> ())


let get_term_graph : unit  ->  tgraph = (fun uu____546 -> (

let uu____547 = (get ())
in uu____547.term_graph))


let get_version : unit  ->  FStar_Syntax_Syntax.version = (fun uu____552 -> (

let uu____553 = (get ())
in uu____553.version))


let set_term_graph : tgraph  ->  unit = (fun tg -> (

let uu____559 = (

let uu___83_560 = (get ())
in {term_graph = tg; univ_graph = uu___83_560.univ_graph; version = uu___83_560.version})
in (set uu____559)))


let chk_v : 'Auu____565 . ('Auu____565 * FStar_Syntax_Syntax.version)  ->  'Auu____565 = (fun uu____574 -> (match (uu____574) with
| (u, v1) -> begin
(

let expected = (get_version ())
in (match (((Prims.op_Equality v1.FStar_Syntax_Syntax.major expected.FStar_Syntax_Syntax.major) && (v1.FStar_Syntax_Syntax.minor <= expected.FStar_Syntax_Syntax.minor))) with
| true -> begin
u
end
| uu____582 -> begin
(

let uu____583 = (

let uu____584 = (version_to_string expected)
in (

let uu____585 = (version_to_string v1)
in (FStar_Util.format2 "Incompatible version for unification variable: current version is %s; got version %s" uu____584 uu____585)))
in (failwith uu____583))
end))
end))


let uvar_id : FStar_Syntax_Syntax.uvar  ->  Prims.int = (fun u -> (

let uu____591 = (get_term_graph ())
in (

let uu____596 = (chk_v u)
in (FStar_Unionfind.puf_id uu____591 uu____596))))


let from_id : Prims.int  ->  FStar_Syntax_Syntax.uvar = (fun n1 -> (

let uu____614 = (

let uu____621 = (get_term_graph ())
in (FStar_Unionfind.puf_fromid uu____621 n1))
in (

let uu____628 = (get_version ())
in ((uu____614), (uu____628)))))


let fresh : unit  ->  FStar_Syntax_Syntax.uvar = (fun uu____639 -> (

let uu____640 = (

let uu____647 = (get_term_graph ())
in (FStar_Unionfind.puf_fresh uu____647 FStar_Pervasives_Native.None))
in (

let uu____654 = (get_version ())
in ((uu____640), (uu____654)))))


let find : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun u -> (

let uu____668 = (get_term_graph ())
in (

let uu____673 = (chk_v u)
in (FStar_Unionfind.puf_find uu____668 uu____673))))


let change : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term  ->  unit = (fun u t -> (

let uu____696 = (

let uu____697 = (get_term_graph ())
in (

let uu____702 = (chk_v u)
in (FStar_Unionfind.puf_change uu____697 uu____702 (FStar_Pervasives_Native.Some (t)))))
in (set_term_graph uu____696)))


let equiv : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.uvar  ->  Prims.bool = (fun u v1 -> (

let uu____725 = (get_term_graph ())
in (

let uu____730 = (chk_v u)
in (

let uu____741 = (chk_v v1)
in (FStar_Unionfind.puf_equivalent uu____725 uu____730 uu____741)))))


let union : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.uvar  ->  unit = (fun u v1 -> (

let uu____764 = (

let uu____765 = (get_term_graph ())
in (

let uu____770 = (chk_v u)
in (

let uu____781 = (chk_v v1)
in (FStar_Unionfind.puf_union uu____765 uu____770 uu____781))))
in (set_term_graph uu____764)))


let get_univ_graph : unit  ->  ugraph = (fun uu____798 -> (

let uu____799 = (get ())
in uu____799.univ_graph))


let set_univ_graph : ugraph  ->  unit = (fun ug -> (

let uu____805 = (

let uu___84_806 = (get ())
in {term_graph = uu___84_806.term_graph; univ_graph = ug; version = uu___84_806.version})
in (set uu____805)))


let univ_uvar_id : FStar_Syntax_Syntax.universe_uvar  ->  Prims.int = (fun u -> (

let uu____812 = (get_univ_graph ())
in (

let uu____817 = (chk_v u)
in (FStar_Unionfind.puf_id uu____812 uu____817))))


let univ_from_id : Prims.int  ->  FStar_Syntax_Syntax.universe_uvar = (fun n1 -> (

let uu____833 = (

let uu____838 = (get_univ_graph ())
in (FStar_Unionfind.puf_fromid uu____838 n1))
in (

let uu____845 = (get_version ())
in ((uu____833), (uu____845)))))


let univ_fresh : unit  ->  FStar_Syntax_Syntax.universe_uvar = (fun uu____854 -> (

let uu____855 = (

let uu____860 = (get_univ_graph ())
in (FStar_Unionfind.puf_fresh uu____860 FStar_Pervasives_Native.None))
in (

let uu____867 = (get_version ())
in ((uu____855), (uu____867)))))


let univ_find : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun u -> (

let uu____879 = (get_univ_graph ())
in (

let uu____884 = (chk_v u)
in (FStar_Unionfind.puf_find uu____879 uu____884))))


let univ_change : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe  ->  unit = (fun u t -> (

let uu____905 = (

let uu____906 = (get_univ_graph ())
in (

let uu____911 = (chk_v u)
in (FStar_Unionfind.puf_change uu____906 uu____911 (FStar_Pervasives_Native.Some (t)))))
in (set_univ_graph uu____905)))


let univ_equiv : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool = (fun u v1 -> (

let uu____932 = (get_univ_graph ())
in (

let uu____937 = (chk_v u)
in (

let uu____946 = (chk_v v1)
in (FStar_Unionfind.puf_equivalent uu____932 uu____937 uu____946)))))


let univ_union : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  unit = (fun u v1 -> (

let uu____967 = (

let uu____968 = (get_univ_graph ())
in (

let uu____973 = (chk_v u)
in (

let uu____982 = (chk_v v1)
in (FStar_Unionfind.puf_union uu____968 uu____973 uu____982))))
in (set_univ_graph uu____967)))




