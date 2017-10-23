open Prims
type vops_t =
  {
  next_major: Prims.unit -> FStar_Syntax_Syntax.version;
  next_minor: Prims.unit -> FStar_Syntax_Syntax.version;}[@@deriving show]
let __proj__Mkvops_t__item__next_major:
  vops_t -> Prims.unit -> FStar_Syntax_Syntax.version =
  fun projectee  ->
    match projectee with
    | { next_major = __fname__next_major; next_minor = __fname__next_minor;_}
        -> __fname__next_major
let __proj__Mkvops_t__item__next_minor:
  vops_t -> Prims.unit -> FStar_Syntax_Syntax.version =
  fun projectee  ->
    match projectee with
    | { next_major = __fname__next_major; next_minor = __fname__next_minor;_}
        -> __fname__next_minor
let vops: vops_t =
  let major = FStar_Util.mk_ref (Prims.parse_int "0") in
  let minor = FStar_Util.mk_ref (Prims.parse_int "0") in
  let next_major uu____56 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____118 = FStar_Util.incr major; FStar_ST.op_Bang major in
     {
       FStar_Syntax_Syntax.major = uu____118;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     }) in
  let next_minor uu____204 =
    let uu____205 = FStar_ST.op_Bang major in
    let uu____266 = FStar_Util.incr minor; FStar_ST.op_Bang minor in
    {
      FStar_Syntax_Syntax.major = uu____205;
      FStar_Syntax_Syntax.minor = uu____266
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
  term_graph: tgraph;
  univ_graph: ugraph;
  version: FStar_Syntax_Syntax.version;}[@@deriving show]
let __proj__Mkuf__item__term_graph: uf -> tgraph =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__term_graph
let __proj__Mkuf__item__univ_graph: uf -> ugraph =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__univ_graph
let __proj__Mkuf__item__version: uf -> FStar_Syntax_Syntax.version =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__version
let empty: FStar_Syntax_Syntax.version -> uf =
  fun v1  ->
    let uu____394 = FStar_Unionfind.puf_empty () in
    let uu____397 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____394; univ_graph = uu____397; version = v1 }
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____404 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____405 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____404 uu____405
let state: uf FStar_ST.ref =
  let uu____415 = let uu____416 = vops.next_major () in empty uu____416 in
  FStar_Util.mk_ref uu____415
type tx =
  | TX of uf[@@deriving show]
let uu___is_TX: tx -> Prims.bool = fun projectee  -> true
let __proj__TX__item___0: tx -> uf =
  fun projectee  -> match projectee with | TX _0 -> _0
let get: Prims.unit -> uf = fun uu____433  -> FStar_ST.op_Bang state
let set: uf -> Prims.unit = fun u  -> FStar_ST.op_Colon_Equals state u
let reset: Prims.unit -> Prims.unit =
  fun uu____533  ->
    let v1 = vops.next_major () in let uu____535 = empty v1 in set uu____535
let new_transaction: Prims.unit -> tx =
  fun uu____539  ->
    let tx = let uu____541 = get () in TX uu____541 in
    (let uu____543 =
       let uu___108_544 = get () in
       let uu____545 = vops.next_minor () in
       {
         term_graph = (uu___108_544.term_graph);
         univ_graph = (uu___108_544.univ_graph);
         version = uu____545
       } in
     set uu____543);
    tx
let commit: tx -> Prims.unit = fun tx  -> ()
let rollback: tx -> Prims.unit =
  fun uu____553  -> match uu____553 with | TX uf -> set uf
let update_in_tx: 'a . 'a FStar_ST.ref -> 'a -> Prims.unit =
  fun r  -> fun x  -> ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____598  -> let uu____599 = get () in uu____599.term_graph
let get_version: Prims.unit -> FStar_Syntax_Syntax.version =
  fun uu____603  -> let uu____604 = get () in uu____604.version
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let uu____609 =
      let uu___109_610 = get () in
      {
        term_graph = tg;
        univ_graph = (uu___109_610.univ_graph);
        version = (uu___109_610.version)
      } in
    set uu____609
let chk_v:
  'Auu____615 .
    ('Auu____615,FStar_Syntax_Syntax.version) FStar_Pervasives_Native.tuple2
      -> 'Auu____615
  =
  fun uu____623  ->
    match uu____623 with
    | (u,v1) ->
        let expected = get_version () in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____632 =
             let uu____633 = version_to_string expected in
             let uu____634 = version_to_string v1 in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____633 uu____634 in
           failwith uu____632)
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____639 = get_term_graph () in
    let uu____644 = chk_v u in FStar_Unionfind.puf_id uu____639 uu____644
let from_id: Prims.int -> FStar_Syntax_Syntax.uvar =
  fun n1  ->
    let uu____661 =
      let uu____666 = get_term_graph () in
      FStar_Unionfind.puf_fromid uu____666 n1 in
    let uu____673 = get_version () in (uu____661, uu____673)
let fresh: Prims.unit -> FStar_Syntax_Syntax.uvar =
  fun uu____681  ->
    let uu____682 =
      let uu____687 = get_term_graph () in
      FStar_Unionfind.puf_fresh uu____687 FStar_Pervasives_Native.None in
    let uu____694 = get_version () in (uu____682, uu____694)
let find:
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____705 = get_term_graph () in
    let uu____710 = chk_v u in FStar_Unionfind.puf_find uu____705 uu____710
let change:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
      let uu____731 =
        let uu____732 = get_term_graph () in
        let uu____737 = chk_v u in
        FStar_Unionfind.puf_change uu____732 uu____737
          (FStar_Pervasives_Native.Some t) in
      set_term_graph uu____731
let equiv: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____758 = get_term_graph () in
      let uu____763 = chk_v u in
      let uu____774 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____758 uu____763 uu____774
let union: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____795 =
        let uu____796 = get_term_graph () in
        let uu____801 = chk_v u in
        let uu____812 = chk_v v1 in
        FStar_Unionfind.puf_union uu____796 uu____801 uu____812 in
      set_term_graph uu____795
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____828  -> let uu____829 = get () in uu____829.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let uu____834 =
      let uu___110_835 = get () in
      {
        term_graph = (uu___110_835.term_graph);
        univ_graph = ug;
        version = (uu___110_835.version)
      } in
    set uu____834
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____840 = get_univ_graph () in
    let uu____845 = chk_v u in FStar_Unionfind.puf_id uu____840 uu____845
let univ_from_id: Prims.int -> FStar_Syntax_Syntax.universe_uvar =
  fun n1  ->
    let uu____860 =
      let uu____865 = get_univ_graph () in
      FStar_Unionfind.puf_fromid uu____865 n1 in
    let uu____872 = get_version () in (uu____860, uu____872)
let univ_fresh: Prims.unit -> FStar_Syntax_Syntax.universe_uvar =
  fun uu____880  ->
    let uu____881 =
      let uu____886 = get_univ_graph () in
      FStar_Unionfind.puf_fresh uu____886 FStar_Pervasives_Native.None in
    let uu____893 = get_version () in (uu____881, uu____893)
let univ_find:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____904 = get_univ_graph () in
    let uu____909 = chk_v u in FStar_Unionfind.puf_find uu____904 uu____909
let univ_change:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
      let uu____928 =
        let uu____929 = get_univ_graph () in
        let uu____934 = chk_v u in
        FStar_Unionfind.puf_change uu____929 uu____934
          (FStar_Pervasives_Native.Some t) in
      set_univ_graph uu____928
let univ_equiv:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____953 = get_univ_graph () in
      let uu____958 = chk_v u in
      let uu____967 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____953 uu____958 uu____967
let univ_union:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____986 =
        let uu____987 = get_univ_graph () in
        let uu____992 = chk_v u in
        let uu____1001 = chk_v v1 in
        FStar_Unionfind.puf_union uu____987 uu____992 uu____1001 in
      set_univ_graph uu____986