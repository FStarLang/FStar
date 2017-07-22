
open Prims
open FStar_Pervasives
type vops_t =
{next_major : Prims.unit  ->  FStar_Syntax_Syntax.version; next_minor : Prims.unit  ->  FStar_Syntax_Syntax.version}


let __proj__Mkvops_t__item__next_major : vops_t  ->  Prims.unit  ->  FStar_Syntax_Syntax.version = (fun projectee -> (match (projectee) with
| {next_major = __fname__next_major; next_minor = __fname__next_minor} -> begin
__fname__next_major
end))


let __proj__Mkvops_t__item__next_minor : vops_t  ->  Prims.unit  ->  FStar_Syntax_Syntax.version = (fun projectee -> (match (projectee) with
| {next_major = __fname__next_major; next_minor = __fname__next_minor} -> begin
__fname__next_minor
end))


let vops : vops_t = (

let major = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let minor = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let next_major = (fun uu____56 -> ((FStar_ST.write minor (Prims.parse_int "0"));
(

let uu____60 = ((FStar_Util.incr major);
(FStar_ST.read major);
)
in {FStar_Syntax_Syntax.major = uu____60; FStar_Syntax_Syntax.minor = (Prims.parse_int "0")});
))
in (

let next_minor = (fun uu____70 -> (

let uu____71 = (FStar_ST.read major)
in (

let uu____74 = ((FStar_Util.incr minor);
(FStar_ST.read minor);
)
in {FStar_Syntax_Syntax.major = uu____71; FStar_Syntax_Syntax.minor = uu____74})))
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

let uu____126 = (FStar_Unionfind.puf_empty ())
in (

let uu____129 = (FStar_Unionfind.puf_empty ())
in {term_graph = uu____126; univ_graph = uu____129; version = v1})))


let version_to_string : FStar_Syntax_Syntax.version  ->  Prims.string = (fun v1 -> (

let uu____136 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major)
in (

let uu____137 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor)
in (FStar_Util.format2 "%s.%s" uu____136 uu____137))))


let state : uf FStar_ST.ref = (

let uu____141 = (

let uu____142 = (vops.next_major ())
in (empty uu____142))
in (FStar_Util.mk_ref uu____141))

type tx =
| TX of uf


let uu___is_TX : tx  ->  Prims.bool = (fun projectee -> true)


let __proj__TX__item___0 : tx  ->  uf = (fun projectee -> (match (projectee) with
| TX (_0) -> begin
_0
end))


let get : Prims.unit  ->  uf = (fun uu____159 -> (FStar_ST.read state))


let set : uf  ->  Prims.unit = (fun u -> (FStar_ST.write state u))


let reset : Prims.unit  ->  Prims.unit = (fun uu____167 -> (

let v1 = (vops.next_major ())
in (

let uu____169 = (empty v1)
in (set uu____169))))


let new_transaction : Prims.unit  ->  tx = (fun uu____173 -> (

let tx = (

let uu____175 = (get ())
in TX (uu____175))
in ((

let uu____177 = (

let uu___100_178 = (get ())
in (

let uu____179 = (vops.next_minor ())
in {term_graph = uu___100_178.term_graph; univ_graph = uu___100_178.univ_graph; version = uu____179}))
in (set uu____177));
tx;
)))


let commit : tx  ->  Prims.unit = (fun tx -> ())


let rollback : tx  ->  Prims.unit = (fun uu____187 -> (match (uu____187) with
| TX (uf) -> begin
(set uf)
end))


let update_in_tx : 'a . 'a FStar_ST.ref  ->  'a  ->  Prims.unit = (fun r x -> ())


let get_term_graph : Prims.unit  ->  tgraph = (fun uu____214 -> (

let uu____215 = (get ())
in uu____215.term_graph))


let get_version : Prims.unit  ->  FStar_Syntax_Syntax.version = (fun uu____219 -> (

let uu____220 = (get ())
in uu____220.version))


let set_term_graph : tgraph  ->  Prims.unit = (fun tg -> (

let uu____225 = (

let uu___101_226 = (get ())
in {term_graph = tg; univ_graph = uu___101_226.univ_graph; version = uu___101_226.version})
in (set uu____225)))


let chk_v : 'Auu____231 . ('Auu____231 * FStar_Syntax_Syntax.version)  ->  'Auu____231 = (fun uu____239 -> (match (uu____239) with
| (u, v1) -> begin
(

let expected = (get_version ())
in (match (((v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major) && (v1.FStar_Syntax_Syntax.minor <= expected.FStar_Syntax_Syntax.minor))) with
| true -> begin
u
end
| uu____247 -> begin
(

let uu____248 = (

let uu____249 = (version_to_string expected)
in (

let uu____250 = (version_to_string v1)
in (FStar_Util.format2 "Incompatible version for unification variable: current version is %s; got version %s" uu____249 uu____250)))
in (failwith uu____248))
end))
end))


let uvar_id : FStar_Syntax_Syntax.uvar  ->  Prims.int = (fun u -> (

let uu____255 = (get_term_graph ())
in (

let uu____260 = (chk_v u)
in (FStar_Unionfind.puf_id uu____255 uu____260))))


let from_id : Prims.int  ->  FStar_Syntax_Syntax.uvar = (fun n1 -> (

let uu____277 = (

let uu____282 = (get_term_graph ())
in (FStar_Unionfind.puf_fromid uu____282 n1))
in (

let uu____289 = (get_version ())
in ((uu____277), (uu____289)))))


let fresh : Prims.unit  ->  FStar_Syntax_Syntax.uvar = (fun uu____297 -> (

let uu____298 = (

let uu____303 = (get_term_graph ())
in (FStar_Unionfind.puf_fresh uu____303 FStar_Pervasives_Native.None))
in (

let uu____310 = (get_version ())
in ((uu____298), (uu____310)))))


let find : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun u -> (

let uu____321 = (get_term_graph ())
in (

let uu____326 = (chk_v u)
in (FStar_Unionfind.puf_find uu____321 uu____326))))


let change : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun u t -> (

let uu____347 = (

let uu____348 = (get_term_graph ())
in (

let uu____353 = (chk_v u)
in (FStar_Unionfind.puf_change uu____348 uu____353 (FStar_Pervasives_Native.Some (t)))))
in (set_term_graph uu____347)))


let equiv : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.uvar  ->  Prims.bool = (fun u v1 -> (

let uu____374 = (get_term_graph ())
in (

let uu____379 = (chk_v u)
in (

let uu____390 = (chk_v v1)
in (FStar_Unionfind.puf_equivalent uu____374 uu____379 uu____390)))))


let union : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.uvar  ->  Prims.unit = (fun u v1 -> (

let uu____411 = (

let uu____412 = (get_term_graph ())
in (

let uu____417 = (chk_v u)
in (

let uu____428 = (chk_v v1)
in (FStar_Unionfind.puf_union uu____412 uu____417 uu____428))))
in (set_term_graph uu____411)))


let get_univ_graph : Prims.unit  ->  ugraph = (fun uu____444 -> (

let uu____445 = (get ())
in uu____445.univ_graph))


let set_univ_graph : ugraph  ->  Prims.unit = (fun ug -> (

let uu____450 = (

let uu___102_451 = (get ())
in {term_graph = uu___102_451.term_graph; univ_graph = ug; version = uu___102_451.version})
in (set uu____450)))


let univ_uvar_id : FStar_Syntax_Syntax.universe_uvar  ->  Prims.int = (fun u -> (

let uu____456 = (get_univ_graph ())
in (

let uu____461 = (chk_v u)
in (FStar_Unionfind.puf_id uu____456 uu____461))))


let univ_from_id : Prims.int  ->  FStar_Syntax_Syntax.universe_uvar = (fun n1 -> (

let uu____476 = (

let uu____481 = (get_univ_graph ())
in (FStar_Unionfind.puf_fromid uu____481 n1))
in (

let uu____488 = (get_version ())
in ((uu____476), (uu____488)))))


let univ_fresh : Prims.unit  ->  FStar_Syntax_Syntax.universe_uvar = (fun uu____496 -> (

let uu____497 = (

let uu____502 = (get_univ_graph ())
in (FStar_Unionfind.puf_fresh uu____502 FStar_Pervasives_Native.None))
in (

let uu____509 = (get_version ())
in ((uu____497), (uu____509)))))


let univ_find : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun u -> (

let uu____520 = (get_univ_graph ())
in (

let uu____525 = (chk_v u)
in (FStar_Unionfind.puf_find uu____520 uu____525))))


let univ_change : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe  ->  Prims.unit = (fun u t -> (

let uu____544 = (

let uu____545 = (get_univ_graph ())
in (

let uu____550 = (chk_v u)
in (FStar_Unionfind.puf_change uu____545 uu____550 (FStar_Pervasives_Native.Some (t)))))
in (set_univ_graph uu____544)))


let univ_equiv : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool = (fun u v1 -> (

let uu____569 = (get_univ_graph ())
in (

let uu____574 = (chk_v u)
in (

let uu____583 = (chk_v v1)
in (FStar_Unionfind.puf_equivalent uu____569 uu____574 uu____583)))))


let univ_union : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.unit = (fun u v1 -> (

let uu____602 = (

let uu____603 = (get_univ_graph ())
in (

let uu____608 = (chk_v u)
in (

let uu____617 = (chk_v v1)
in (FStar_Unionfind.puf_union uu____603 uu____608 uu____617))))
in (set_univ_graph uu____602)))




