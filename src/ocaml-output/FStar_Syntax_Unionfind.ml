open Prims
type vops_t =
  {
  next_major: unit -> FStar_Syntax_Syntax.version ;
  next_minor: unit -> FStar_Syntax_Syntax.version }
let (__proj__Mkvops_t__item__next_major :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee ->
    match projectee with | { next_major; next_minor;_} -> next_major
let (__proj__Mkvops_t__item__next_minor :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee ->
    match projectee with | { next_major; next_minor;_} -> next_minor
let (vops : vops_t) =
  let major = FStar_Util.mk_ref Prims.int_zero in
  let minor = FStar_Util.mk_ref Prims.int_zero in
  let next_major uu____78 =
    FStar_ST.op_Colon_Equals minor Prims.int_zero;
    (let uu____86 = FStar_Util.incr major; FStar_ST.op_Bang major in
     {
       FStar_Syntax_Syntax.major = uu____86;
       FStar_Syntax_Syntax.minor = Prims.int_zero
     }) in
  let next_minor uu____99 =
    let uu____100 = FStar_ST.op_Bang major in
    let uu____107 = FStar_Util.incr minor; FStar_ST.op_Bang minor in
    {
      FStar_Syntax_Syntax.major = uu____100;
      FStar_Syntax_Syntax.minor = uu____107
    } in
  { next_major; next_minor }
type tgraph =
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option FStar_Unionfind.puf
type ugraph =
  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.puf
type uf =
  {
  term_graph: tgraph ;
  univ_graph: ugraph ;
  version: FStar_Syntax_Syntax.version ;
  ro: Prims.bool }
let (__proj__Mkuf__item__term_graph : uf -> tgraph) =
  fun projectee ->
    match projectee with
    | { term_graph; univ_graph; version; ro;_} -> term_graph
let (__proj__Mkuf__item__univ_graph : uf -> ugraph) =
  fun projectee ->
    match projectee with
    | { term_graph; univ_graph; version; ro;_} -> univ_graph
let (__proj__Mkuf__item__version : uf -> FStar_Syntax_Syntax.version) =
  fun projectee ->
    match projectee with
    | { term_graph; univ_graph; version; ro;_} -> version
let (__proj__Mkuf__item__ro : uf -> Prims.bool) =
  fun projectee ->
    match projectee with | { term_graph; univ_graph; version; ro;_} -> ro
let (empty : FStar_Syntax_Syntax.version -> uf) =
  fun v ->
    let uu____184 = FStar_Unionfind.puf_empty () in
    let uu____187 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____184; univ_graph = uu____187; version = v; ro = false
    }
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v ->
    let uu____195 = FStar_Util.string_of_int v.FStar_Syntax_Syntax.major in
    let uu____196 = FStar_Util.string_of_int v.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____195 uu____196
let (state : uf FStar_ST.ref) =
  let uu____199 = let uu____200 = vops.next_major () in empty uu____200 in
  FStar_Util.mk_ref uu____199
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee -> true
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee -> match projectee with | TX _0 -> _0
let (get : unit -> uf) = fun uu____221 -> FStar_ST.op_Bang state
let (set_ro : unit -> unit) =
  fun uu____232 ->
    let s = get () in
    FStar_ST.op_Colon_Equals state
      (let uu___34_241 = s in
       {
         term_graph = (uu___34_241.term_graph);
         univ_graph = (uu___34_241.univ_graph);
         version = (uu___34_241.version);
         ro = true
       })
let (set_rw : unit -> unit) =
  fun uu____246 ->
    let s = get () in
    FStar_ST.op_Colon_Equals state
      (let uu___38_255 = s in
       {
         term_graph = (uu___38_255.term_graph);
         univ_graph = (uu___38_255.univ_graph);
         version = (uu___38_255.version);
         ro = false
       })
let with_uf_enabled : 'a . (unit -> 'a) -> 'a =
  fun f ->
    let s = get () in
    set_rw ();
    (let restore uu____278 = if s.ro then set_ro () else () in
     let r =
       let uu____281 = FStar_Options.trace_error () in
       if uu____281
       then f ()
       else
         (try (fun uu___50_284 -> match () with | () -> f ()) ()
          with | uu___49_287 -> (restore (); FStar_Exn.raise uu___49_287)) in
     restore (); r)
let (fail_if_ro : unit -> unit) =
  fun uu____294 ->
    let uu____295 = let uu____296 = get () in uu____296.ro in
    if uu____295
    then
      FStar_Errors.raise_error
        (FStar_Errors.Fatal_BadUvar,
          "Internal error: UF graph was in read-only mode")
        FStar_Range.dummyRange
    else ()
let (set : uf -> unit) =
  fun u -> fail_if_ro (); FStar_ST.op_Colon_Equals state u
let (reset : unit -> unit) =
  fun uu____314 ->
    fail_if_ro ();
    (let v = vops.next_major () in
     let uu____317 =
       let uu___65_318 = empty v in
       {
         term_graph = (uu___65_318.term_graph);
         univ_graph = (uu___65_318.univ_graph);
         version = (uu___65_318.version);
         ro = false
       } in
     set uu____317)
let (new_transaction : unit -> tx) =
  fun uu____323 ->
    let tx1 = let uu____325 = get () in TX uu____325 in
    (let uu____327 =
       let uu___69_328 = get () in
       let uu____329 = vops.next_minor () in
       {
         term_graph = (uu___69_328.term_graph);
         univ_graph = (uu___69_328.univ_graph);
         version = uu____329;
         ro = (uu___69_328.ro)
       } in
     set uu____327);
    tx1
let (commit : tx -> unit) = fun tx1 -> ()
let (rollback : tx -> unit) =
  fun uu____339 -> match uu____339 with | TX uf1 -> set uf1
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit = fun r -> fun x -> ()
let (get_term_graph : unit -> tgraph) =
  fun uu____366 -> let uu____367 = get () in uu____367.term_graph
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____372 -> let uu____373 = get () in uu____373.version
let (set_term_graph : tgraph -> unit) =
  fun tg ->
    let uu____379 =
      let uu___82_380 = get () in
      {
        term_graph = tg;
        univ_graph = (uu___82_380.univ_graph);
        version = (uu___82_380.version);
        ro = (uu___82_380.ro)
      } in
    set uu____379
let (chk_v_t :
  (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version * FStar_Range.range)
    ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
      FStar_Unionfind.p_uvar)
  =
  fun uu____399 ->
    match uu____399 with
    | (u, v, rng) ->
        let uvar_to_string u1 =
          let uu____439 =
            let uu____440 =
              let uu____441 = get_term_graph () in
              FStar_Unionfind.puf_id uu____441 u1 in
            FStar_All.pipe_right uu____440 FStar_Util.string_of_int in
          Prims.op_Hat "?" uu____439 in
        let expected = get_version () in
        if
          (v.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____454 =
             let uu____459 =
               let uu____460 = uvar_to_string u in
               let uu____461 = version_to_string expected in
               let uu____462 = version_to_string v in
               FStar_Util.format3
                 "Internal error: incompatible version for term unification variable %s: current version is %s; got version %s"
                 uu____460 uu____461 uu____462 in
             (FStar_Errors.Fatal_BadUvar, uu____459) in
           FStar_Errors.raise_error uu____454 rng)
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u ->
    let uu____472 = get_term_graph () in
    let uu____477 = chk_v_t u in FStar_Unionfind.puf_id uu____472 uu____477
let (fresh : FStar_Range.range -> FStar_Syntax_Syntax.uvar) =
  fun rng ->
    fail_if_ro ();
    (let uu____490 =
       let uu____497 = get_term_graph () in
       FStar_Unionfind.puf_fresh uu____497 FStar_Pervasives_Native.None in
     let uu____504 = get_version () in (uu____490, uu____504, rng))
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u ->
    let uu____518 = get_term_graph () in
    let uu____523 = chk_v_t u in FStar_Unionfind.puf_find uu____518 uu____523
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u ->
    fun t ->
      let uu____540 =
        let uu____541 = get_term_graph () in
        let uu____546 = chk_v_t u in
        FStar_Unionfind.puf_change uu____541 uu____546
          (FStar_Pervasives_Native.Some t) in
      set_term_graph uu____540
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u ->
    fun v ->
      let uu____563 = get_term_graph () in
      let uu____568 = chk_v_t u in
      let uu____573 = chk_v_t v in
      FStar_Unionfind.puf_equivalent uu____563 uu____568 uu____573
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u ->
    fun v ->
      let uu____590 =
        let uu____591 = get_term_graph () in
        let uu____596 = chk_v_t u in
        let uu____601 = chk_v_t v in
        FStar_Unionfind.puf_union uu____591 uu____596 uu____601 in
      set_term_graph uu____590
let (get_univ_graph : unit -> ugraph) =
  fun uu____612 -> let uu____613 = get () in uu____613.univ_graph
let (chk_v_u :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version * FStar_Range.range)
    ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
      FStar_Unionfind.p_uvar)
  =
  fun uu____632 ->
    match uu____632 with
    | (u, v, rng) ->
        let uvar_to_string u1 =
          let uu____672 =
            let uu____673 =
              let uu____674 = get_univ_graph () in
              FStar_Unionfind.puf_id uu____674 u1 in
            FStar_All.pipe_right uu____673 FStar_Util.string_of_int in
          Prims.op_Hat "?" uu____672 in
        let expected = get_version () in
        if
          (v.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____687 =
             let uu____692 =
               let uu____693 = uvar_to_string u in
               let uu____694 = version_to_string expected in
               let uu____695 = version_to_string v in
               FStar_Util.format3
                 "Internal error: incompatible version for universe unification variable %s: current version is %s; got version %s"
                 uu____693 uu____694 uu____695 in
             (FStar_Errors.Fatal_BadUvar, uu____692) in
           FStar_Errors.raise_error uu____687 rng)
let (set_univ_graph : ugraph -> unit) =
  fun ug ->
    let uu____705 =
      let uu___112_706 = get () in
      {
        term_graph = (uu___112_706.term_graph);
        univ_graph = ug;
        version = (uu___112_706.version);
        ro = (uu___112_706.ro)
      } in
    set uu____705
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u ->
    let uu____712 = get_univ_graph () in
    let uu____717 = chk_v_u u in FStar_Unionfind.puf_id uu____712 uu____717
let (univ_fresh : FStar_Range.range -> FStar_Syntax_Syntax.universe_uvar) =
  fun rng ->
    fail_if_ro ();
    (let uu____730 =
       let uu____735 = get_univ_graph () in
       FStar_Unionfind.puf_fresh uu____735 FStar_Pervasives_Native.None in
     let uu____742 = get_version () in (uu____730, uu____742, rng))
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u ->
    let uu____754 = get_univ_graph () in
    let uu____759 = chk_v_u u in FStar_Unionfind.puf_find uu____754 uu____759
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u ->
    fun t ->
      let uu____776 =
        let uu____777 = get_univ_graph () in
        let uu____782 = chk_v_u u in
        FStar_Unionfind.puf_change uu____777 uu____782
          (FStar_Pervasives_Native.Some t) in
      set_univ_graph uu____776
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u ->
    fun v ->
      let uu____799 = get_univ_graph () in
      let uu____804 = chk_v_u u in
      let uu____809 = chk_v_u v in
      FStar_Unionfind.puf_equivalent uu____799 uu____804 uu____809
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u ->
    fun v ->
      let uu____826 =
        let uu____827 = get_univ_graph () in
        let uu____832 = chk_v_u u in
        let uu____837 = chk_v_u v in
        FStar_Unionfind.puf_union uu____827 uu____832 uu____837 in
      set_univ_graph uu____826