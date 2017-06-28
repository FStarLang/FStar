
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

let uu____122 = (FStar_Unionfind.puf_empty ())
in (

let uu____124 = (FStar_Unionfind.puf_empty ())
in {term_graph = uu____122; univ_graph = uu____124; version = v1})))


let version_to_string : FStar_Syntax_Syntax.version  ->  Prims.string = (fun v1 -> (

let uu____130 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major)
in (

let uu____131 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor)
in (FStar_Util.format2 "%s.%s" uu____130 uu____131))))


let state : uf FStar_ST.ref = (

let uu____134 = (

let uu____135 = (vops.next_major ())
in (empty uu____135))
in (FStar_Util.mk_ref uu____134))

type tx =
| TX of uf


let uu___is_TX : tx  ->  Prims.bool = (fun projectee -> true)


let __proj__TX__item___0 : tx  ->  uf = (fun projectee -> (match (projectee) with
| TX (_0) -> begin
_0
end))


let get : Prims.unit  ->  uf = (fun uu____153 -> (FStar_ST.read state))


let set : uf  ->  Prims.unit = (fun u -> (FStar_ST.write state u))


let reset : Prims.unit  ->  Prims.unit = (fun uu____165 -> (

let v1 = (vops.next_major ())
in (

let uu____167 = (empty v1)
in (set uu____167))))


let new_transaction : Prims.unit  ->  tx = (fun uu____171 -> (

let tx = (

let uu____173 = (get ())
in TX (uu____173))
in ((

let uu____175 = (

let uu___100_176 = (get ())
in (

let uu____177 = (vops.next_minor ())
in {term_graph = uu___100_176.term_graph; univ_graph = uu___100_176.univ_graph; version = uu____177}))
in (set uu____175));
tx;
)))


let commit : tx  ->  Prims.unit = (fun tx -> ())


let rollback : tx  ->  Prims.unit = (fun uu____185 -> (match (uu____185) with
| TX (uf) -> begin
(set uf)
end))


let update_in_tx = (fun r x -> ())


let get_term_graph : Prims.unit  ->  tgraph = (fun uu____210 -> (

let uu____211 = (get ())
in uu____211.term_graph))


let get_version : Prims.unit  ->  FStar_Syntax_Syntax.version = (fun uu____215 -> (

let uu____216 = (get ())
in uu____216.version))


let set_term_graph : tgraph  ->  Prims.unit = (fun tg -> (

let uu____221 = (

let uu___101_222 = (get ())
in {term_graph = tg; univ_graph = uu___101_222.univ_graph; version = uu___101_222.version})
in (set uu____221)))


let chk_v = (fun uu____233 -> (match (uu____233) with
| (u, v1) -> begin
(

let expected = (get_version ())
in (match (((v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major) && (v1.FStar_Syntax_Syntax.minor <= expected.FStar_Syntax_Syntax.minor))) with
| true -> begin
u
end
| uu____239 -> begin
(

let uu____240 = (

let uu____241 = (version_to_string expected)
in (

let uu____242 = (version_to_string v1)
in (FStar_Util.format2 "Incompatible version for unification variable: current version is %s; got version %s" uu____241 uu____242)))
in (failwith uu____240))
end))
end))


let uvar_id : FStar_Syntax_Syntax.uvar  ->  Prims.int = (fun u -> (

let uu____247 = (get_term_graph ())
in (

let uu____250 = (chk_v u)
in (FStar_Unionfind.puf_id uu____247 uu____250))))


let from_id : Prims.int  ->  FStar_Syntax_Syntax.uvar = (fun n1 -> (

let uu____262 = (

let uu____265 = (get_term_graph ())
in (FStar_Unionfind.puf_fromid uu____265 n1))
in (

let uu____269 = (get_version ())
in ((uu____262), (uu____269)))))


let fresh : Prims.unit  ->  FStar_Syntax_Syntax.uvar = (fun uu____275 -> (

let uu____276 = (

let uu____279 = (get_term_graph ())
in (FStar_Unionfind.puf_fresh uu____279 FStar_Pervasives_Native.None))
in (

let uu____283 = (get_version ())
in ((uu____276), (uu____283)))))


let find : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun u -> (

let uu____291 = (get_term_graph ())
in (

let uu____294 = (chk_v u)
in (FStar_Unionfind.puf_find uu____291 uu____294))))


let change : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun u t -> (

let uu____310 = (

let uu____311 = (get_term_graph ())
in (

let uu____314 = (chk_v u)
in (FStar_Unionfind.puf_change uu____311 uu____314 (FStar_Pervasives_Native.Some (t)))))
in (set_term_graph uu____310)))


let equiv : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.uvar  ->  Prims.bool = (fun u v1 -> (

let uu____330 = (get_term_graph ())
in (

let uu____333 = (chk_v u)
in (

let uu____340 = (chk_v v1)
in (FStar_Unionfind.puf_equivalent uu____330 uu____333 uu____340)))))


let union : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.uvar  ->  Prims.unit = (fun u v1 -> (

let uu____356 = (

let uu____357 = (get_term_graph ())
in (

let uu____360 = (chk_v u)
in (

let uu____367 = (chk_v v1)
in (FStar_Unionfind.puf_union uu____357 uu____360 uu____367))))
in (set_term_graph uu____356)))


let get_univ_graph : Prims.unit  ->  ugraph = (fun uu____378 -> (

let uu____379 = (get ())
in uu____379.univ_graph))


let set_univ_graph : ugraph  ->  Prims.unit = (fun ug -> (

let uu____384 = (

let uu___102_385 = (get ())
in {term_graph = uu___102_385.term_graph; univ_graph = ug; version = uu___102_385.version})
in (set uu____384)))


let univ_uvar_id : FStar_Syntax_Syntax.universe_uvar  ->  Prims.int = (fun u -> (

let uu____390 = (get_univ_graph ())
in (

let uu____393 = (chk_v u)
in (FStar_Unionfind.puf_id uu____390 uu____393))))


let univ_from_id : Prims.int  ->  FStar_Syntax_Syntax.universe_uvar = (fun n1 -> (

let uu____403 = (

let uu____406 = (get_univ_graph ())
in (FStar_Unionfind.puf_fromid uu____406 n1))
in (

let uu____410 = (get_version ())
in ((uu____403), (uu____410)))))


let univ_fresh : Prims.unit  ->  FStar_Syntax_Syntax.universe_uvar = (fun uu____416 -> (

let uu____417 = (

let uu____420 = (get_univ_graph ())
in (FStar_Unionfind.puf_fresh uu____420 FStar_Pervasives_Native.None))
in (

let uu____424 = (get_version ())
in ((uu____417), (uu____424)))))


let univ_find : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun u -> (

let uu____432 = (get_univ_graph ())
in (

let uu____435 = (chk_v u)
in (FStar_Unionfind.puf_find uu____432 uu____435))))


let univ_change : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe  ->  Prims.unit = (fun u t -> (

let uu____449 = (

let uu____450 = (get_univ_graph ())
in (

let uu____453 = (chk_v u)
in (FStar_Unionfind.puf_change uu____450 uu____453 (FStar_Pervasives_Native.Some (t)))))
in (set_univ_graph uu____449)))


let univ_equiv : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool = (fun u v1 -> (

let uu____467 = (get_univ_graph ())
in (

let uu____470 = (chk_v u)
in (

let uu____475 = (chk_v v1)
in (FStar_Unionfind.puf_equivalent uu____467 uu____470 uu____475)))))


let univ_union : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.unit = (fun u v1 -> (

let uu____489 = (

let uu____490 = (get_univ_graph ())
in (

let uu____493 = (chk_v u)
in (

let uu____498 = (chk_v v1)
in (FStar_Unionfind.puf_union uu____490 uu____493 uu____498))))
in (set_univ_graph uu____489)))




