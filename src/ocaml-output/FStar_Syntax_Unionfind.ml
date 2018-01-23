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
  let next_major uu____52 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____95 = FStar_Util.incr major; FStar_ST.op_Bang major in
     {
       FStar_Syntax_Syntax.major = uu____95;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     }) in
  let next_minor uu____174 =
    let uu____175 = FStar_ST.op_Bang major in
    let uu____217 = FStar_Util.incr minor; FStar_ST.op_Bang minor in
    {
      FStar_Syntax_Syntax.major = uu____175;
      FStar_Syntax_Syntax.minor = uu____217
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
    let uu____334 = FStar_Unionfind.puf_empty () in
    let uu____337 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____334; univ_graph = uu____337; version = v1 }
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____343 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____344 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____343 uu____344
let state: uf FStar_ST.ref =
  let uu____358 = let uu____359 = vops.next_major () in empty uu____359 in
  FStar_Util.mk_ref uu____358
type tx =
  | TX of uf[@@deriving show]
let uu___is_TX: tx -> Prims.bool = fun projectee  -> true
let __proj__TX__item___0: tx -> uf =
  fun projectee  -> match projectee with | TX _0 -> _0
let get: Prims.unit -> uf = fun uu____373  -> FStar_ST.op_Bang state
let set: uf -> Prims.unit = fun u  -> FStar_ST.op_Colon_Equals state u
let reset: Prims.unit -> Prims.unit =
  fun uu____417  ->
    let v1 = vops.next_major () in let uu____419 = empty v1 in set uu____419
let new_transaction: Prims.unit -> tx =
  fun uu____422  ->
    let tx = let uu____424 = get () in TX uu____424 in
    (let uu____426 =
       let uu___23_427 = get () in
       let uu____428 = vops.next_minor () in
       {
         term_graph = (uu___23_427.term_graph);
         univ_graph = (uu___23_427.univ_graph);
         version = uu____428
       } in
     set uu____426);
    tx
let commit: tx -> Prims.unit = fun tx  -> ()
let rollback: tx -> Prims.unit =
  fun uu____434  -> match uu____434 with | TX uf -> set uf
let update_in_tx: 'a . 'a FStar_ST.ref -> 'a -> Prims.unit =
  fun r  -> fun x  -> ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____487  -> let uu____488 = get () in uu____488.term_graph
let get_version: Prims.unit -> FStar_Syntax_Syntax.version =
  fun uu____491  -> let uu____492 = get () in uu____492.version
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let uu____496 =
      let uu___24_497 = get () in
      {
        term_graph = tg;
        univ_graph = (uu___24_497.univ_graph);
        version = (uu___24_497.version)
      } in
    set uu____496
let chk_v:
  'Auu____500 .
    ('Auu____500,FStar_Syntax_Syntax.version) FStar_Pervasives_Native.tuple2
      -> 'Auu____500
  =
  fun uu____508  ->
    match uu____508 with
    | (u,v1) ->
        let expected = get_version () in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____517 =
             let uu____518 = version_to_string expected in
             let uu____519 = version_to_string v1 in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____518 uu____519 in
           failwith uu____517)
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____523 = get_term_graph () in
    let uu____528 = chk_v u in FStar_Unionfind.puf_id uu____523 uu____528
let from_id: Prims.int -> FStar_Syntax_Syntax.uvar =
  fun n1  ->
    let uu____544 =
      let uu____549 = get_term_graph () in
      FStar_Unionfind.puf_fromid uu____549 n1 in
    let uu____556 = get_version () in (uu____544, uu____556)
let fresh: Prims.unit -> FStar_Syntax_Syntax.uvar =
  fun uu____563  ->
    let uu____564 =
      let uu____569 = get_term_graph () in
      FStar_Unionfind.puf_fresh uu____569 FStar_Pervasives_Native.None in
    let uu____576 = get_version () in (uu____564, uu____576)
let find:
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____586 = get_term_graph () in
    let uu____591 = chk_v u in FStar_Unionfind.puf_find uu____586 uu____591
let change:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
      let uu____610 =
        let uu____611 = get_term_graph () in
        let uu____616 = chk_v u in
        FStar_Unionfind.puf_change uu____611 uu____616
          (FStar_Pervasives_Native.Some t) in
      set_term_graph uu____610
let equiv: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____635 = get_term_graph () in
      let uu____640 = chk_v u in
      let uu____651 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____635 uu____640 uu____651
let union: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____670 =
        let uu____671 = get_term_graph () in
        let uu____676 = chk_v u in
        let uu____687 = chk_v v1 in
        FStar_Unionfind.puf_union uu____671 uu____676 uu____687 in
      set_term_graph uu____670
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____702  -> let uu____703 = get () in uu____703.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let uu____707 =
      let uu___25_708 = get () in
      {
        term_graph = (uu___25_708.term_graph);
        univ_graph = ug;
        version = (uu___25_708.version)
      } in
    set uu____707
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____712 = get_univ_graph () in
    let uu____717 = chk_v u in FStar_Unionfind.puf_id uu____712 uu____717
let univ_from_id: Prims.int -> FStar_Syntax_Syntax.universe_uvar =
  fun n1  ->
    let uu____731 =
      let uu____736 = get_univ_graph () in
      FStar_Unionfind.puf_fromid uu____736 n1 in
    let uu____743 = get_version () in (uu____731, uu____743)
let univ_fresh: Prims.unit -> FStar_Syntax_Syntax.universe_uvar =
  fun uu____750  ->
    let uu____751 =
      let uu____756 = get_univ_graph () in
      FStar_Unionfind.puf_fresh uu____756 FStar_Pervasives_Native.None in
    let uu____763 = get_version () in (uu____751, uu____763)
let univ_find:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____773 = get_univ_graph () in
    let uu____778 = chk_v u in FStar_Unionfind.puf_find uu____773 uu____778
let univ_change:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
      let uu____795 =
        let uu____796 = get_univ_graph () in
        let uu____801 = chk_v u in
        FStar_Unionfind.puf_change uu____796 uu____801
          (FStar_Pervasives_Native.Some t) in
      set_univ_graph uu____795
let univ_equiv:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____818 = get_univ_graph () in
      let uu____823 = chk_v u in
      let uu____832 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____818 uu____823 uu____832
let univ_union:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____849 =
        let uu____850 = get_univ_graph () in
        let uu____855 = chk_v u in
        let uu____864 = chk_v v1 in
        FStar_Unionfind.puf_union uu____850 uu____855 uu____864 in
      set_univ_graph uu____849