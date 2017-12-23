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
    (let uu____124 = FStar_Util.incr major; FStar_ST.op_Bang major in
     {
       FStar_Syntax_Syntax.major = uu____124;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     }) in
  let next_minor uu____232 =
    let uu____233 = FStar_ST.op_Bang major in
    let uu____304 = FStar_Util.incr minor; FStar_ST.op_Bang minor in
    {
      FStar_Syntax_Syntax.major = uu____233;
      FStar_Syntax_Syntax.minor = uu____304
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
    let uu____450 = FStar_Unionfind.puf_empty () in
    let uu____453 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____450; univ_graph = uu____453; version = v1 }
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____459 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____460 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____459 uu____460
let state: uf FStar_ST.ref =
  let uu____474 = let uu____475 = vops.next_major () in empty uu____475 in
  FStar_Util.mk_ref uu____474
type tx =
  | TX of uf[@@deriving show]
let uu___is_TX: tx -> Prims.bool = fun projectee  -> true
let __proj__TX__item___0: tx -> uf =
  fun projectee  -> match projectee with | TX _0 -> _0
let get: Prims.unit -> uf = fun uu____489  -> FStar_ST.op_Bang state
let set: uf -> Prims.unit = fun u  -> FStar_ST.op_Colon_Equals state u
let reset: Prims.unit -> Prims.unit =
  fun uu____591  ->
    let v1 = vops.next_major () in let uu____593 = empty v1 in set uu____593
let new_transaction: Prims.unit -> tx =
  fun uu____596  ->
    let tx = let uu____598 = get () in TX uu____598 in
    (let uu____600 =
       let uu___22_601 = get () in
       let uu____602 = vops.next_minor () in
       {
         term_graph = (uu___22_601.term_graph);
         univ_graph = (uu___22_601.univ_graph);
         version = uu____602
       } in
     set uu____600);
    tx
let commit: tx -> Prims.unit = fun tx  -> ()
let rollback: tx -> Prims.unit =
  fun uu____608  -> match uu____608 with | TX uf -> set uf
let update_in_tx: 'a . 'a FStar_ST.ref -> 'a -> Prims.unit =
  fun r  -> fun x  -> ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____661  -> let uu____662 = get () in uu____662.term_graph
let get_version: Prims.unit -> FStar_Syntax_Syntax.version =
  fun uu____665  -> let uu____666 = get () in uu____666.version
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let uu____670 =
      let uu___23_671 = get () in
      {
        term_graph = tg;
        univ_graph = (uu___23_671.univ_graph);
        version = (uu___23_671.version)
      } in
    set uu____670
let chk_v:
  'Auu____674 .
    ('Auu____674,FStar_Syntax_Syntax.version) FStar_Pervasives_Native.tuple2
      -> 'Auu____674
  =
  fun uu____682  ->
    match uu____682 with
    | (u,v1) ->
        let expected = get_version () in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____691 =
             let uu____692 = version_to_string expected in
             let uu____693 = version_to_string v1 in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____692 uu____693 in
           failwith uu____691)
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____697 = get_term_graph () in
    let uu____702 = chk_v u in FStar_Unionfind.puf_id uu____697 uu____702
let from_id: Prims.int -> FStar_Syntax_Syntax.uvar =
  fun n1  ->
    let uu____718 =
      let uu____723 = get_term_graph () in
      FStar_Unionfind.puf_fromid uu____723 n1 in
    let uu____730 = get_version () in (uu____718, uu____730)
let fresh: Prims.unit -> FStar_Syntax_Syntax.uvar =
  fun uu____737  ->
    let uu____738 =
      let uu____743 = get_term_graph () in
      FStar_Unionfind.puf_fresh uu____743 FStar_Pervasives_Native.None in
    let uu____750 = get_version () in (uu____738, uu____750)
let find:
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____760 = get_term_graph () in
    let uu____765 = chk_v u in FStar_Unionfind.puf_find uu____760 uu____765
let change:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
      let uu____784 =
        let uu____785 = get_term_graph () in
        let uu____790 = chk_v u in
        FStar_Unionfind.puf_change uu____785 uu____790
          (FStar_Pervasives_Native.Some t) in
      set_term_graph uu____784
let equiv: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____809 = get_term_graph () in
      let uu____814 = chk_v u in
      let uu____825 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____809 uu____814 uu____825
let union: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____844 =
        let uu____845 = get_term_graph () in
        let uu____850 = chk_v u in
        let uu____861 = chk_v v1 in
        FStar_Unionfind.puf_union uu____845 uu____850 uu____861 in
      set_term_graph uu____844
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____876  -> let uu____877 = get () in uu____877.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let uu____881 =
      let uu___24_882 = get () in
      {
        term_graph = (uu___24_882.term_graph);
        univ_graph = ug;
        version = (uu___24_882.version)
      } in
    set uu____881
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____886 = get_univ_graph () in
    let uu____891 = chk_v u in FStar_Unionfind.puf_id uu____886 uu____891
let univ_from_id: Prims.int -> FStar_Syntax_Syntax.universe_uvar =
  fun n1  ->
    let uu____905 =
      let uu____910 = get_univ_graph () in
      FStar_Unionfind.puf_fromid uu____910 n1 in
    let uu____917 = get_version () in (uu____905, uu____917)
let univ_fresh: Prims.unit -> FStar_Syntax_Syntax.universe_uvar =
  fun uu____924  ->
    let uu____925 =
      let uu____930 = get_univ_graph () in
      FStar_Unionfind.puf_fresh uu____930 FStar_Pervasives_Native.None in
    let uu____937 = get_version () in (uu____925, uu____937)
let univ_find:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____947 = get_univ_graph () in
    let uu____952 = chk_v u in FStar_Unionfind.puf_find uu____947 uu____952
let univ_change:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
      let uu____969 =
        let uu____970 = get_univ_graph () in
        let uu____975 = chk_v u in
        FStar_Unionfind.puf_change uu____970 uu____975
          (FStar_Pervasives_Native.Some t) in
      set_univ_graph uu____969
let univ_equiv:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____992 = get_univ_graph () in
      let uu____997 = chk_v u in
      let uu____1006 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____992 uu____997 uu____1006
let univ_union:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____1023 =
        let uu____1024 = get_univ_graph () in
        let uu____1029 = chk_v u in
        let uu____1038 = chk_v v1 in
        FStar_Unionfind.puf_union uu____1024 uu____1029 uu____1038 in
      set_univ_graph uu____1023