open Prims
type vops_t =
  {
  next_major: Prims.unit -> FStar_Syntax_Syntax.version;
  next_minor: Prims.unit -> FStar_Syntax_Syntax.version;}
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
    FStar_ST.write minor (Prims.parse_int "0");
    (let uu____60 = FStar_Util.incr major; FStar_ST.read major in
     {
       FStar_Syntax_Syntax.major = uu____60;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     }) in
  let next_minor uu____70 =
    let uu____71 = FStar_ST.read major in
    let uu____74 = FStar_Util.incr minor; FStar_ST.read minor in
    {
      FStar_Syntax_Syntax.major = uu____71;
      FStar_Syntax_Syntax.minor = uu____74
    } in
  { next_major; next_minor }
type tgraph =
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option FStar_Unionfind.puf
type ugraph =
  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.puf
type uf =
  {
  term_graph: tgraph;
  univ_graph: ugraph;
  version: FStar_Syntax_Syntax.version;}
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
    let uu____126 = FStar_Unionfind.puf_empty () in
    let uu____129 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____126; univ_graph = uu____129; version = v1 }
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____136 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____137 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____136 uu____137
let state: uf FStar_ST.ref =
  let uu____141 = let uu____142 = vops.next_major () in empty uu____142 in
  FStar_Util.mk_ref uu____141
type tx =
  | TX of uf
let uu___is_TX: tx -> Prims.bool = fun projectee  -> true
let __proj__TX__item___0: tx -> uf =
  fun projectee  -> match projectee with | TX _0 -> _0
let get: Prims.unit -> uf = fun uu____159  -> FStar_ST.read state
let set: uf -> Prims.unit = fun u  -> FStar_ST.write state u
let reset: Prims.unit -> Prims.unit =
  fun uu____167  ->
    let v1 = vops.next_major () in let uu____169 = empty v1 in set uu____169
let new_transaction: Prims.unit -> tx =
  fun uu____173  ->
    let tx = let uu____175 = get () in TX uu____175 in
    (let uu____177 =
       let uu___100_178 = get () in
       let uu____179 = vops.next_minor () in
       {
         term_graph = (uu___100_178.term_graph);
         univ_graph = (uu___100_178.univ_graph);
         version = uu____179
       } in
     set uu____177);
    tx
let commit: tx -> Prims.unit = fun tx  -> ()
let rollback: tx -> Prims.unit =
  fun uu____187  -> match uu____187 with | TX uf -> set uf
let update_in_tx r x = ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____214  -> let uu____215 = get () in uu____215.term_graph
let get_version: Prims.unit -> FStar_Syntax_Syntax.version =
  fun uu____219  -> let uu____220 = get () in uu____220.version
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let uu____225 =
      let uu___101_226 = get () in
      {
        term_graph = tg;
        univ_graph = (uu___101_226.univ_graph);
        version = (uu___101_226.version)
      } in
    set uu____225
let chk_v uu____239 =
  match uu____239 with
  | (u,v1) ->
      let expected = get_version () in
      if
        (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
          &&
          (v1.FStar_Syntax_Syntax.minor <= expected.FStar_Syntax_Syntax.minor)
      then u
      else
        (let uu____248 =
           let uu____249 = version_to_string expected in
           let uu____250 = version_to_string v1 in
           FStar_Util.format2
             "Incompatible version for unification variable: current version is %s; got version %s"
             uu____249 uu____250 in
         failwith uu____248)
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____255 = get_term_graph () in
    let uu____260 = chk_v u in FStar_Unionfind.puf_id uu____255 uu____260
let from_id:
  Prims.int ->
    (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
       FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
      FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    let uu____279 =
      let uu____284 = get_term_graph () in
      FStar_Unionfind.puf_fromid uu____284 n1 in
    let uu____291 = get_version () in (uu____279, uu____291)
let fresh:
  Prims.unit ->
    (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
       FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____299  ->
    let uu____300 =
      let uu____305 = get_term_graph () in
      FStar_Unionfind.puf_fresh uu____305 FStar_Pervasives_Native.None in
    let uu____312 = get_version () in (uu____300, uu____312)
let find:
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____323 = get_term_graph () in
    let uu____328 = chk_v u in FStar_Unionfind.puf_find uu____323 uu____328
let change:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
      let uu____351 =
        let uu____352 = get_term_graph () in
        let uu____357 = chk_v u in
        FStar_Unionfind.puf_change uu____352 uu____357
          (FStar_Pervasives_Native.Some t) in
      set_term_graph uu____351
let equiv: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____380 = get_term_graph () in
      let uu____385 = chk_v u in
      let uu____398 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____380 uu____385 uu____398
let union: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____421 =
        let uu____422 = get_term_graph () in
        let uu____427 = chk_v u in
        let uu____440 = chk_v v1 in
        FStar_Unionfind.puf_union uu____422 uu____427 uu____440 in
      set_term_graph uu____421
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____458  -> let uu____459 = get () in uu____459.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let uu____464 =
      let uu___102_465 = get () in
      {
        term_graph = (uu___102_465.term_graph);
        univ_graph = ug;
        version = (uu___102_465.version)
      } in
    set uu____464
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____470 = get_univ_graph () in
    let uu____475 = chk_v u in FStar_Unionfind.puf_id uu____470 uu____475
let univ_from_id:
  Prims.int ->
    (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
       FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
      FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    let uu____490 =
      let uu____495 = get_univ_graph () in
      FStar_Unionfind.puf_fromid uu____495 n1 in
    let uu____502 = get_version () in (uu____490, uu____502)
let univ_fresh:
  Prims.unit ->
    (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
       FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
      FStar_Pervasives_Native.tuple2
  =
  fun uu____510  ->
    let uu____511 =
      let uu____516 = get_univ_graph () in
      FStar_Unionfind.puf_fresh uu____516 FStar_Pervasives_Native.None in
    let uu____523 = get_version () in (uu____511, uu____523)
let univ_find:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____534 = get_univ_graph () in
    let uu____539 = chk_v u in FStar_Unionfind.puf_find uu____534 uu____539
let univ_change:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
      let uu____558 =
        let uu____559 = get_univ_graph () in
        let uu____564 = chk_v u in
        FStar_Unionfind.puf_change uu____559 uu____564
          (FStar_Pervasives_Native.Some t) in
      set_univ_graph uu____558
let univ_equiv:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____583 = get_univ_graph () in
      let uu____588 = chk_v u in
      let uu____597 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____583 uu____588 uu____597
let univ_union:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____616 =
        let uu____617 = get_univ_graph () in
        let uu____622 = chk_v u in
        let uu____631 = chk_v v1 in
        FStar_Unionfind.puf_union uu____617 uu____622 uu____631 in
      set_univ_graph uu____616