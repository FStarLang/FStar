open Prims
type vops_t =
  {
  next_major: unit -> FStar_Syntax_Syntax.version ;
  next_minor: unit -> FStar_Syntax_Syntax.version }
let (__proj__Mkvops_t__item__next_major :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with | { next_major; next_minor;_} -> next_major
  
let (__proj__Mkvops_t__item__next_minor :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with | { next_major; next_minor;_} -> next_minor
  
let (vops : vops_t) =
  let major = FStar_Util.mk_ref Prims.int_zero  in
  let minor = FStar_Util.mk_ref Prims.int_zero  in
  let next_major uu____86 =
    FStar_ST.op_Colon_Equals minor Prims.int_zero;
    (let uu____110 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____110;
       FStar_Syntax_Syntax.minor = Prims.int_zero
     })
     in
  let next_minor uu____140 =
    let uu____141 = FStar_ST.op_Bang major  in
    let uu____164 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____141;
      FStar_Syntax_Syntax.minor = uu____164
    }  in
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
  fun projectee  ->
    match projectee with
    | { term_graph; univ_graph; version; ro;_} -> term_graph
  
let (__proj__Mkuf__item__univ_graph : uf -> ugraph) =
  fun projectee  ->
    match projectee with
    | { term_graph; univ_graph; version; ro;_} -> univ_graph
  
let (__proj__Mkuf__item__version : uf -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with
    | { term_graph; univ_graph; version; ro;_} -> version
  
let (__proj__Mkuf__item__ro : uf -> Prims.bool) =
  fun projectee  ->
    match projectee with | { term_graph; univ_graph; version; ro;_} -> ro
  
let (empty : FStar_Syntax_Syntax.version -> uf) =
  fun v  ->
    let uu____269 = FStar_Unionfind.puf_empty ()  in
    let uu____272 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____269; univ_graph = uu____272; version = v; ro = false
    }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v  ->
    let uu____283 = FStar_Util.string_of_int v.FStar_Syntax_Syntax.major  in
    let uu____285 = FStar_Util.string_of_int v.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____283 uu____285
  
let (state : uf FStar_ST.ref) =
  let uu____291 = let uu____292 = vops.next_major ()  in empty uu____292  in
  FStar_Util.mk_ref uu____291 
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____318  -> FStar_ST.op_Bang state 
let (set_ro : unit -> unit) =
  fun uu____343  ->
    let s = get ()  in
    FStar_ST.op_Colon_Equals state
      (let uu___34_365 = s  in
       {
         term_graph = (uu___34_365.term_graph);
         univ_graph = (uu___34_365.univ_graph);
         version = (uu___34_365.version);
         ro = true
       })
  
let (set_rw : unit -> unit) =
  fun uu____372  ->
    let s = get ()  in
    FStar_ST.op_Colon_Equals state
      (let uu___38_394 = s  in
       {
         term_graph = (uu___38_394.term_graph);
         univ_graph = (uu___38_394.univ_graph);
         version = (uu___38_394.version);
         ro = false
       })
  
let with_uf_enabled : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    let s = get ()  in
    set_rw ();
    (let restore uu____419 = if s.ro then set_ro () else ()  in
     let r =
       try (fun uu___49_425  -> match () with | () -> f ()) ()
       with | uu___48_428 -> (restore (); FStar_Exn.raise uu___48_428)  in
     restore (); r)
  
let (fail_if_ro : unit -> unit) =
  fun uu____436  ->
    let uu____437 = let uu____439 = get ()  in uu____439.ro  in
    if uu____437
    then
      FStar_Errors.raise_error
        (FStar_Errors.Fatal_BadUvar,
          "Internal error: UF graph was in read-only mode")
        FStar_Range.dummyRange
    else ()
  
let (set : uf -> unit) =
  fun u  -> fail_if_ro (); FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____476  ->
    fail_if_ro ();
    (let v = vops.next_major ()  in
     let uu____479 =
       let uu___64_480 = empty v  in
       {
         term_graph = (uu___64_480.term_graph);
         univ_graph = (uu___64_480.univ_graph);
         version = (uu___64_480.version);
         ro = false
       }  in
     set uu____479)
  
let (new_transaction : unit -> tx) =
  fun uu____487  ->
    let tx1 = let uu____489 = get ()  in TX uu____489  in
    (let uu____491 =
       let uu___68_492 = get ()  in
       let uu____493 = vops.next_minor ()  in
       {
         term_graph = (uu___68_492.term_graph);
         univ_graph = (uu___68_492.univ_graph);
         version = uu____493;
         ro = (uu___68_492.ro)
       }  in
     set uu____491);
    tx1
  
let (commit : tx -> unit) = fun tx1  -> () 
let (rollback : tx -> unit) =
  fun uu____505  -> match uu____505 with | TX uf1 -> set uf1 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____534  -> let uu____535 = get ()  in uu____535.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____541  -> let uu____542 = get ()  in uu____542.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____549 =
      let uu___81_550 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___81_550.univ_graph);
        version = (uu___81_550.version);
        ro = (uu___81_550.ro)
      }  in
    set uu____549
  
let (chk_v_t :
  (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version * FStar_Range.range)
    ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
      FStar_Unionfind.p_uvar)
  =
  fun uu____570  ->
    match uu____570 with
    | (u,v,rng) ->
        let uvar_to_string u1 =
          let uu____611 =
            let uu____613 =
              let uu____615 = get_term_graph ()  in
              FStar_Unionfind.puf_id uu____615 u1  in
            FStar_All.pipe_right uu____613 FStar_Util.string_of_int  in
          Prims.op_Hat "?" uu____611  in
        let expected = get_version ()  in
        if
          (v.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____634 =
             let uu____640 =
               let uu____642 = uvar_to_string u  in
               let uu____644 = version_to_string expected  in
               let uu____646 = version_to_string v  in
               FStar_Util.format3
                 "Internal error: incompatible version for term unification variable %s: current version is %s; got version %s"
                 uu____642 uu____644 uu____646
                in
             (FStar_Errors.Fatal_BadUvar, uu____640)  in
           FStar_Errors.raise_error uu____634 rng)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____661 = get_term_graph ()  in
    let uu____666 = chk_v_t u  in FStar_Unionfind.puf_id uu____661 uu____666
  
let (fresh : FStar_Range.range -> FStar_Syntax_Syntax.uvar) =
  fun rng  ->
    fail_if_ro ();
    (let uu____680 =
       let uu____687 = get_term_graph ()  in
       FStar_Unionfind.puf_fresh uu____687 FStar_Pervasives_Native.None  in
     let uu____694 = get_version ()  in (uu____680, uu____694, rng))
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____709 = get_term_graph ()  in
    let uu____714 = chk_v_t u  in
    FStar_Unionfind.puf_find uu____709 uu____714
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____732 =
        let uu____733 = get_term_graph ()  in
        let uu____738 = chk_v_t u  in
        FStar_Unionfind.puf_change uu____733 uu____738
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____732
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v  ->
      let uu____757 = get_term_graph ()  in
      let uu____762 = chk_v_t u  in
      let uu____767 = chk_v_t v  in
      FStar_Unionfind.puf_equivalent uu____757 uu____762 uu____767
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v  ->
      let uu____785 =
        let uu____786 = get_term_graph ()  in
        let uu____791 = chk_v_t u  in
        let uu____796 = chk_v_t v  in
        FStar_Unionfind.puf_union uu____786 uu____791 uu____796  in
      set_term_graph uu____785
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____808  -> let uu____809 = get ()  in uu____809.univ_graph 
let (chk_v_u :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version * FStar_Range.range)
    ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
      FStar_Unionfind.p_uvar)
  =
  fun uu____829  ->
    match uu____829 with
    | (u,v,rng) ->
        let uvar_to_string u1 =
          let uu____870 =
            let uu____872 =
              let uu____874 = get_univ_graph ()  in
              FStar_Unionfind.puf_id uu____874 u1  in
            FStar_All.pipe_right uu____872 FStar_Util.string_of_int  in
          Prims.op_Hat "?" uu____870  in
        let expected = get_version ()  in
        if
          (v.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____893 =
             let uu____899 =
               let uu____901 = uvar_to_string u  in
               let uu____903 = version_to_string expected  in
               let uu____905 = version_to_string v  in
               FStar_Util.format3
                 "Internal error: incompatible version for universe unification variable %s: current version is %s; got version %s"
                 uu____901 uu____903 uu____905
                in
             (FStar_Errors.Fatal_BadUvar, uu____899)  in
           FStar_Errors.raise_error uu____893 rng)
  
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____919 =
      let uu___111_920 = get ()  in
      {
        term_graph = (uu___111_920.term_graph);
        univ_graph = ug;
        version = (uu___111_920.version);
        ro = (uu___111_920.ro)
      }  in
    set uu____919
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____928 = get_univ_graph ()  in
    let uu____933 = chk_v_u u  in FStar_Unionfind.puf_id uu____928 uu____933
  
let (univ_fresh : FStar_Range.range -> FStar_Syntax_Syntax.universe_uvar) =
  fun rng  ->
    fail_if_ro ();
    (let uu____947 =
       let uu____952 = get_univ_graph ()  in
       FStar_Unionfind.puf_fresh uu____952 FStar_Pervasives_Native.None  in
     let uu____959 = get_version ()  in (uu____947, uu____959, rng))
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____972 = get_univ_graph ()  in
    let uu____977 = chk_v_u u  in
    FStar_Unionfind.puf_find uu____972 uu____977
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____995 =
        let uu____996 = get_univ_graph ()  in
        let uu____1001 = chk_v_u u  in
        FStar_Unionfind.puf_change uu____996 uu____1001
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____995
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v  ->
      let uu____1020 = get_univ_graph ()  in
      let uu____1025 = chk_v_u u  in
      let uu____1030 = chk_v_u v  in
      FStar_Unionfind.puf_equivalent uu____1020 uu____1025 uu____1030
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v  ->
      let uu____1048 =
        let uu____1049 = get_univ_graph ()  in
        let uu____1054 = chk_v_u u  in
        let uu____1059 = chk_v_u v  in
        FStar_Unionfind.puf_union uu____1049 uu____1054 uu____1059  in
      set_univ_graph uu____1048
  