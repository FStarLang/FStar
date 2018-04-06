
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

let next_major = (fun uu____52 -> ((FStar_ST.op_Colon_Equals minor (Prims.parse_int "0"));
(

let uu____149 = ((FStar_Util.incr major);
(FStar_ST.op_Bang major);
)
in {FStar_Syntax_Syntax.major = uu____149; FStar_Syntax_Syntax.minor = (Prims.parse_int "0")});
))
in (

let next_minor = (fun uu____354 -> (

let uu____355 = (FStar_ST.op_Bang major)
in (

let uu____451 = ((FStar_Util.incr minor);
(FStar_ST.op_Bang minor);
)
in {FStar_Syntax_Syntax.major = uu____355; FStar_Syntax_Syntax.minor = uu____451})))
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

let uu____694 = (FStar_Unionfind.puf_empty ())
in (

let uu____697 = (FStar_Unionfind.puf_empty ())
in {term_graph = uu____694; univ_graph = uu____697; version = v1})))


let version_to_string : FStar_Syntax_Syntax.version  ->  Prims.string = (fun v1 -> (

let uu____703 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major)
in (

let uu____704 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor)
in (FStar_Util.format2 "%s.%s" uu____703 uu____704))))


let state : uf FStar_ST.ref = (

let uu____742 = (

let uu____743 = (vops.next_major ())
in (empty uu____743))
in (FStar_Util.mk_ref uu____742))

type tx =
| TX of uf


let uu___is_TX : tx  ->  Prims.bool = (fun projectee -> true)


let __proj__TX__item___0 : tx  ->  uf = (fun projectee -> (match (projectee) with
| TX (_0) -> begin
_0
end))


let get : Prims.unit  ->  uf = (fun uu____757 -> (FStar_ST.op_Bang state))


let set : uf  ->  Prims.unit = (fun u -> (FStar_ST.op_Colon_Equals state u))


let reset : Prims.unit  ->  Prims.unit = (fun uu____813 -> (

let v1 = (vops.next_major ())
in (

let uu____815 = (empty v1)
in (set uu____815))))


let new_transaction : Prims.unit  ->  tx = (fun uu____818 -> (

let tx = (

let uu____820 = (get ())
in TX (uu____820))
in ((

let uu____822 = (

let uu___26_823 = (get ())
in (

let uu____824 = (vops.next_minor ())
in {term_graph = uu___26_823.term_graph; univ_graph = uu___26_823.univ_graph; version = uu____824}))
in (set uu____822));
tx;
)))


let commit : tx  ->  Prims.unit = (fun tx -> ())


let rollback : tx  ->  Prims.unit = (fun uu____830 -> (match (uu____830) with
| TX (uf) -> begin
(set uf)
end))


let update_in_tx : 'a . 'a FStar_ST.ref  ->  'a  ->  Prims.unit = (fun r x -> ())


let get_term_graph : Prims.unit  ->  tgraph = (fun uu____955 -> (

let uu____956 = (get ())
in uu____956.term_graph))


let get_version : Prims.unit  ->  FStar_Syntax_Syntax.version = (fun uu____959 -> (

let uu____960 = (get ())
in uu____960.version))


let set_term_graph : tgraph  ->  Prims.unit = (fun tg -> (

let uu____964 = (

let uu___27_965 = (get ())
in {term_graph = tg; univ_graph = uu___27_965.univ_graph; version = uu___27_965.version})
in (set uu____964)))


let chk_v : 'Auu____968 . ('Auu____968 * FStar_Syntax_Syntax.version)  ->  'Auu____968 = (fun uu____976 -> (match (uu____976) with
| (u, v1) -> begin
(

let expected = (get_version ())
in (match (((Prims.op_Equality v1.FStar_Syntax_Syntax.major expected.FStar_Syntax_Syntax.major) && (v1.FStar_Syntax_Syntax.minor <= expected.FStar_Syntax_Syntax.minor))) with
| true -> begin
u
end
| uu____984 -> begin
(

let uu____985 = (

let uu____986 = (version_to_string expected)
in (

let uu____987 = (version_to_string v1)
in (FStar_Util.format2 "Incompatible version for unification variable: current version is %s; got version %s" uu____986 uu____987)))
in (failwith uu____985))
end))
end))


let uvar_id : FStar_Syntax_Syntax.uvar  ->  Prims.int = (fun u -> (

let uu____991 = (get_term_graph ())
in (

let uu____996 = (chk_v u)
in (FStar_Unionfind.puf_id uu____991 uu____996))))


let from_id : Prims.int  ->  FStar_Syntax_Syntax.uvar = (fun n1 -> (

let uu____1012 = (

let uu____1017 = (get_term_graph ())
in (FStar_Unionfind.puf_fromid uu____1017 n1))
in (

let uu____1024 = (get_version ())
in ((uu____1012), (uu____1024)))))


let fresh : Prims.unit  ->  FStar_Syntax_Syntax.uvar = (fun uu____1031 -> (

let uu____1032 = (

let uu____1037 = (get_term_graph ())
in (FStar_Unionfind.puf_fresh uu____1037 FStar_Pervasives_Native.None))
in (

let uu____1044 = (get_version ())
in ((uu____1032), (uu____1044)))))


let find : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun u -> (

let uu____1054 = (get_term_graph ())
in (

let uu____1059 = (chk_v u)
in (FStar_Unionfind.puf_find uu____1054 uu____1059))))


let change : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun u t -> (

let uu____1078 = (

let uu____1079 = (get_term_graph ())
in (

let uu____1084 = (chk_v u)
in (FStar_Unionfind.puf_change uu____1079 uu____1084 (FStar_Pervasives_Native.Some (t)))))
in (set_term_graph uu____1078)))


let equiv : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.uvar  ->  Prims.bool = (fun u v1 -> (

let uu____1103 = (get_term_graph ())
in (

let uu____1108 = (chk_v u)
in (

let uu____1119 = (chk_v v1)
in (FStar_Unionfind.puf_equivalent uu____1103 uu____1108 uu____1119)))))


let union : FStar_Syntax_Syntax.uvar  ->  FStar_Syntax_Syntax.uvar  ->  Prims.unit = (fun u v1 -> (

let uu____1138 = (

let uu____1139 = (get_term_graph ())
in (

let uu____1144 = (chk_v u)
in (

let uu____1155 = (chk_v v1)
in (FStar_Unionfind.puf_union uu____1139 uu____1144 uu____1155))))
in (set_term_graph uu____1138)))


let get_univ_graph : Prims.unit  ->  ugraph = (fun uu____1170 -> (

let uu____1171 = (get ())
in uu____1171.univ_graph))


let set_univ_graph : ugraph  ->  Prims.unit = (fun ug -> (

let uu____1175 = (

let uu___28_1176 = (get ())
in {term_graph = uu___28_1176.term_graph; univ_graph = ug; version = uu___28_1176.version})
in (set uu____1175)))


let univ_uvar_id : FStar_Syntax_Syntax.universe_uvar  ->  Prims.int = (fun u -> (

let uu____1180 = (get_univ_graph ())
in (

let uu____1185 = (chk_v u)
in (FStar_Unionfind.puf_id uu____1180 uu____1185))))


let univ_from_id : Prims.int  ->  FStar_Syntax_Syntax.universe_uvar = (fun n1 -> (

let uu____1199 = (

let uu____1204 = (get_univ_graph ())
in (FStar_Unionfind.puf_fromid uu____1204 n1))
in (

let uu____1211 = (get_version ())
in ((uu____1199), (uu____1211)))))


let univ_fresh : Prims.unit  ->  FStar_Syntax_Syntax.universe_uvar = (fun uu____1218 -> (

let uu____1219 = (

let uu____1224 = (get_univ_graph ())
in (FStar_Unionfind.puf_fresh uu____1224 FStar_Pervasives_Native.None))
in (

let uu____1231 = (get_version ())
in ((uu____1219), (uu____1231)))))


let univ_find : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option = (fun u -> (

let uu____1241 = (get_univ_graph ())
in (

let uu____1246 = (chk_v u)
in (FStar_Unionfind.puf_find uu____1241 uu____1246))))


let univ_change : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe  ->  Prims.unit = (fun u t -> (

let uu____1263 = (

let uu____1264 = (get_univ_graph ())
in (

let uu____1269 = (chk_v u)
in (FStar_Unionfind.puf_change uu____1264 uu____1269 (FStar_Pervasives_Native.Some (t)))))
in (set_univ_graph uu____1263)))


let univ_equiv : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool = (fun u v1 -> (

let uu____1286 = (get_univ_graph ())
in (

let uu____1291 = (chk_v u)
in (

let uu____1300 = (chk_v v1)
in (FStar_Unionfind.puf_equivalent uu____1286 uu____1291 uu____1300)))))


let univ_union : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.unit = (fun u v1 -> (

let uu____1317 = (

let uu____1318 = (get_univ_graph ())
in (

let uu____1323 = (chk_v u)
in (

let uu____1332 = (chk_v v1)
in (FStar_Unionfind.puf_union uu____1318 uu____1323 uu____1332))))
in (set_univ_graph uu____1317)))




