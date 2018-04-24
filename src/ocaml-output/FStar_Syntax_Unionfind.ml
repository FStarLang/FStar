open Prims
type vops_t =
  {
  next_major: unit -> FStar_Syntax_Syntax.version ;
  next_minor: unit -> FStar_Syntax_Syntax.version }[@@deriving show]
let (__proj__Mkvops_t__item__next_major :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee ->
    match projectee with
    | { next_major = __fname__next_major; next_minor = __fname__next_minor;_}
        -> __fname__next_major
let (__proj__Mkvops_t__item__next_minor :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee ->
    match projectee with
    | { next_major = __fname__next_major; next_minor = __fname__next_minor;_}
        -> __fname__next_minor
let (vops : vops_t) =
  let major = FStar_Util.mk_ref (Prims.parse_int "0") in
  let minor = FStar_Util.mk_ref (Prims.parse_int "0") in
  let next_major uu____72 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____173 = FStar_Util.incr major; FStar_ST.op_Bang major in
     {
       FStar_Syntax_Syntax.major = uu____173;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     }) in
  let next_minor uu____384 =
    let uu____385 = FStar_ST.op_Bang major in
    let uu____485 = FStar_Util.incr minor; FStar_ST.op_Bang minor in
    {
      FStar_Syntax_Syntax.major = uu____385;
      FStar_Syntax_Syntax.minor = uu____485
    } in
  { next_major; next_minor }
type tgraph =
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option FStar_Unionfind.puf
[@@deriving show]
type ugraph =
  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.puf[@@deriving show]
type uf =
  {
  term_graph: tgraph ;
  univ_graph: ugraph ;
  version: FStar_Syntax_Syntax.version }[@@deriving show]
let (__proj__Mkuf__item__term_graph : uf -> tgraph) =
  fun projectee ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__term_graph
let (__proj__Mkuf__item__univ_graph : uf -> ugraph) =
  fun projectee ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__univ_graph
let (__proj__Mkuf__item__version : uf -> FStar_Syntax_Syntax.version) =
  fun projectee ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__version
let (empty : FStar_Syntax_Syntax.version -> uf) =
  fun v1 ->
    let uu____743 = FStar_Unionfind.puf_empty () in
    let uu____746 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____743; univ_graph = uu____746; version = v1 }
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1 ->
    let uu____754 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____755 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____754 uu____755
let (state : uf FStar_ST.ref) =
  let uu____793 = let uu____794 = vops.next_major () in empty uu____794 in
  FStar_Util.mk_ref uu____793
type tx =
  | TX of uf [@@deriving show]
let (uu___is_TX : tx -> Prims.bool) = fun projectee -> true
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee -> match projectee with | TX _0 -> _0
let (get : unit -> uf) = fun uu____815 -> FStar_ST.op_Bang state
let (set : uf -> unit) = fun u -> FStar_ST.op_Colon_Equals state u
let (reset : unit -> unit) =
  fun uu____883 ->
    let v1 = vops.next_major () in let uu____885 = empty v1 in set uu____885
let (new_transaction : unit -> tx) =
  fun uu____890 ->
    let tx = let uu____892 = get () in TX uu____892 in
    (let uu____894 =
       let uu___28_895 = get () in
       let uu____896 = vops.next_minor () in
       {
         term_graph = (uu___28_895.term_graph);
         univ_graph = (uu___28_895.univ_graph);
         version = uu____896
       } in
     set uu____894);
    tx
let (commit : tx -> unit) = fun tx -> ()
let (rollback : tx -> unit) =
  fun uu____906 -> match uu____906 with | TX uf -> set uf
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit = fun r -> fun x -> ()
let (get_term_graph : unit -> tgraph) =
  fun uu____1038 -> let uu____1039 = get () in uu____1039.term_graph
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____1044 -> let uu____1045 = get () in uu____1045.version
let (set_term_graph : tgraph -> unit) =
  fun tg ->
    let uu____1051 =
      let uu___29_1052 = get () in
      {
        term_graph = tg;
        univ_graph = (uu___29_1052.univ_graph);
        version = (uu___29_1052.version)
      } in
    set uu____1051
let chk_v :
  'Auu____1057 .
    ('Auu____1057, FStar_Syntax_Syntax.version)
      FStar_Pervasives_Native.tuple2 -> 'Auu____1057
  =
  fun uu____1066 ->
    match uu____1066 with
    | (u, v1) ->
        let expected = get_version () in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____1075 =
             let uu____1076 = version_to_string expected in
             let uu____1077 = version_to_string v1 in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____1076 uu____1077 in
           failwith uu____1075)
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u ->
    let uu____1083 = get_term_graph () in
    let uu____1088 = chk_v u in FStar_Unionfind.puf_id uu____1083 uu____1088
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1 ->
    let uu____1106 =
      let uu____1111 = get_term_graph () in
      FStar_Unionfind.puf_fromid uu____1111 n1 in
    let uu____1118 = get_version () in (uu____1106, uu____1118)
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____1127 ->
    let uu____1128 =
      let uu____1133 = get_term_graph () in
      FStar_Unionfind.puf_fresh uu____1133 FStar_Pervasives_Native.None in
    let uu____1140 = get_version () in (uu____1128, uu____1140)
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u ->
    let uu____1152 = get_term_graph () in
    let uu____1157 = chk_v u in
    FStar_Unionfind.puf_find uu____1152 uu____1157
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u ->
    fun t ->
      let uu____1180 =
        let uu____1181 = get_term_graph () in
        let uu____1186 = chk_v u in
        FStar_Unionfind.puf_change uu____1181 uu____1186
          (FStar_Pervasives_Native.Some t) in
      set_term_graph uu____1180
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u ->
    fun v1 ->
      let uu____1209 = get_term_graph () in
      let uu____1214 = chk_v u in
      let uu____1225 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____1209 uu____1214 uu____1225
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u ->
    fun v1 ->
      let uu____1248 =
        let uu____1249 = get_term_graph () in
        let uu____1254 = chk_v u in
        let uu____1265 = chk_v v1 in
        FStar_Unionfind.puf_union uu____1249 uu____1254 uu____1265 in
      set_term_graph uu____1248
let (get_univ_graph : unit -> ugraph) =
  fun uu____1282 -> let uu____1283 = get () in uu____1283.univ_graph
let (set_univ_graph : ugraph -> unit) =
  fun ug ->
    let uu____1289 =
      let uu___30_1290 = get () in
      {
        term_graph = (uu___30_1290.term_graph);
        univ_graph = ug;
        version = (uu___30_1290.version)
      } in
    set uu____1289
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u ->
    let uu____1296 = get_univ_graph () in
    let uu____1301 = chk_v u in FStar_Unionfind.puf_id uu____1296 uu____1301
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1 ->
    let uu____1317 =
      let uu____1322 = get_univ_graph () in
      FStar_Unionfind.puf_fromid uu____1322 n1 in
    let uu____1329 = get_version () in (uu____1317, uu____1329)
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____1338 ->
    let uu____1339 =
      let uu____1344 = get_univ_graph () in
      FStar_Unionfind.puf_fresh uu____1344 FStar_Pervasives_Native.None in
    let uu____1351 = get_version () in (uu____1339, uu____1351)
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u ->
    let uu____1363 = get_univ_graph () in
    let uu____1368 = chk_v u in
    FStar_Unionfind.puf_find uu____1363 uu____1368
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u ->
    fun t ->
      let uu____1389 =
        let uu____1390 = get_univ_graph () in
        let uu____1395 = chk_v u in
        FStar_Unionfind.puf_change uu____1390 uu____1395
          (FStar_Pervasives_Native.Some t) in
      set_univ_graph uu____1389
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u ->
    fun v1 ->
      let uu____1416 = get_univ_graph () in
      let uu____1421 = chk_v u in
      let uu____1430 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____1416 uu____1421 uu____1430
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u ->
    fun v1 ->
      let uu____1451 =
        let uu____1452 = get_univ_graph () in
        let uu____1457 = chk_v u in
        let uu____1466 = chk_v v1 in
        FStar_Unionfind.puf_union uu____1452 uu____1457 uu____1466 in
      set_univ_graph uu____1451