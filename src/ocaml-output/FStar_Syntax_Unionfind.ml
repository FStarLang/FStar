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
       let uu____424 = FStar_Options.trace_error ()  in
       if uu____424
       then f ()
       else
         (try (fun uu___50_430  -> match () with | () -> f ()) ()
          with | uu___49_433 -> (restore (); FStar_Exn.raise uu___49_433))
        in
     restore (); r)
  
let (fail_if_ro : unit -> unit) =
  fun uu____441  ->
    let uu____442 = let uu____444 = get ()  in uu____444.ro  in
    if uu____442
    then
      FStar_Errors.raise_error
        (FStar_Errors.Fatal_BadUvar,
          "Internal error: UF graph was in read-only mode")
        FStar_Range.dummyRange
    else ()
  
let (set : uf -> unit) =
  fun u  -> fail_if_ro (); FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____481  ->
    fail_if_ro ();
    (let v = vops.next_major ()  in
     let uu____484 =
       let uu___65_485 = empty v  in
       {
         term_graph = (uu___65_485.term_graph);
         univ_graph = (uu___65_485.univ_graph);
         version = (uu___65_485.version);
         ro = false
       }  in
     set uu____484)
  
let (new_transaction : unit -> tx) =
  fun uu____492  ->
    let tx1 = let uu____494 = get ()  in TX uu____494  in
    (let uu____496 =
       let uu___69_497 = get ()  in
       let uu____498 = vops.next_minor ()  in
       {
         term_graph = (uu___69_497.term_graph);
         univ_graph = (uu___69_497.univ_graph);
         version = uu____498;
         ro = (uu___69_497.ro)
       }  in
     set uu____496);
    tx1
  
let (commit : tx -> unit) = fun tx1  -> () 
let (rollback : tx -> unit) =
  fun uu____510  -> match uu____510 with | TX uf1 -> set uf1 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____539  -> let uu____540 = get ()  in uu____540.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____546  -> let uu____547 = get ()  in uu____547.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____554 =
      let uu___82_555 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___82_555.univ_graph);
        version = (uu___82_555.version);
        ro = (uu___82_555.ro)
      }  in
    set uu____554
  
let (chk_v_t :
  (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version * FStar_Range.range)
    ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
      FStar_Unionfind.p_uvar)
  =
  fun uu____575  ->
    match uu____575 with
    | (u,v,rng) ->
        let uvar_to_string u1 =
          let uu____616 =
            let uu____618 =
              let uu____620 = get_term_graph ()  in
              FStar_Unionfind.puf_id uu____620 u1  in
            FStar_All.pipe_right uu____618 FStar_Util.string_of_int  in
          Prims.op_Hat "?" uu____616  in
        let expected = get_version ()  in
        if
          (v.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____639 =
             let uu____645 =
               let uu____647 = uvar_to_string u  in
               let uu____649 = version_to_string expected  in
               let uu____651 = version_to_string v  in
               FStar_Util.format3
                 "Internal error: incompatible version for term unification variable %s: current version is %s; got version %s"
                 uu____647 uu____649 uu____651
                in
             (FStar_Errors.Fatal_BadUvar, uu____645)  in
           FStar_Errors.raise_error uu____639 rng)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____666 = get_term_graph ()  in
    let uu____671 = chk_v_t u  in FStar_Unionfind.puf_id uu____666 uu____671
  
let (fresh : FStar_Range.range -> FStar_Syntax_Syntax.uvar) =
  fun rng  ->
    fail_if_ro ();
    (let uu____685 =
       let uu____692 = get_term_graph ()  in
       FStar_Unionfind.puf_fresh uu____692 FStar_Pervasives_Native.None  in
     let uu____699 = get_version ()  in (uu____685, uu____699, rng))
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____714 = get_term_graph ()  in
    let uu____719 = chk_v_t u  in
    FStar_Unionfind.puf_find uu____714 uu____719
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____737 =
        let uu____738 = get_term_graph ()  in
        let uu____743 = chk_v_t u  in
        FStar_Unionfind.puf_change uu____738 uu____743
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____737
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v  ->
      let uu____762 = get_term_graph ()  in
      let uu____767 = chk_v_t u  in
      let uu____772 = chk_v_t v  in
      FStar_Unionfind.puf_equivalent uu____762 uu____767 uu____772
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v  ->
      let uu____790 =
        let uu____791 = get_term_graph ()  in
        let uu____796 = chk_v_t u  in
        let uu____801 = chk_v_t v  in
        FStar_Unionfind.puf_union uu____791 uu____796 uu____801  in
      set_term_graph uu____790
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____813  -> let uu____814 = get ()  in uu____814.univ_graph 
let (chk_v_u :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version * FStar_Range.range)
    ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
      FStar_Unionfind.p_uvar)
  =
  fun uu____834  ->
    match uu____834 with
    | (u,v,rng) ->
        let uvar_to_string u1 =
          let uu____875 =
            let uu____877 =
              let uu____879 = get_univ_graph ()  in
              FStar_Unionfind.puf_id uu____879 u1  in
            FStar_All.pipe_right uu____877 FStar_Util.string_of_int  in
          Prims.op_Hat "?" uu____875  in
        let expected = get_version ()  in
        if
          (v.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____898 =
             let uu____904 =
               let uu____906 = uvar_to_string u  in
               let uu____908 = version_to_string expected  in
               let uu____910 = version_to_string v  in
               FStar_Util.format3
                 "Internal error: incompatible version for universe unification variable %s: current version is %s; got version %s"
                 uu____906 uu____908 uu____910
                in
             (FStar_Errors.Fatal_BadUvar, uu____904)  in
           FStar_Errors.raise_error uu____898 rng)
  
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____924 =
      let uu___112_925 = get ()  in
      {
        term_graph = (uu___112_925.term_graph);
        univ_graph = ug;
        version = (uu___112_925.version);
        ro = (uu___112_925.ro)
      }  in
    set uu____924
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____933 = get_univ_graph ()  in
    let uu____938 = chk_v_u u  in FStar_Unionfind.puf_id uu____933 uu____938
  
let (univ_fresh : FStar_Range.range -> FStar_Syntax_Syntax.universe_uvar) =
  fun rng  ->
    fail_if_ro ();
    (let uu____952 =
       let uu____957 = get_univ_graph ()  in
       FStar_Unionfind.puf_fresh uu____957 FStar_Pervasives_Native.None  in
     let uu____964 = get_version ()  in (uu____952, uu____964, rng))
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____977 = get_univ_graph ()  in
    let uu____982 = chk_v_u u  in
    FStar_Unionfind.puf_find uu____977 uu____982
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____1000 =
        let uu____1001 = get_univ_graph ()  in
        let uu____1006 = chk_v_u u  in
        FStar_Unionfind.puf_change uu____1001 uu____1006
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____1000
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v  ->
      let uu____1025 = get_univ_graph ()  in
      let uu____1030 = chk_v_u u  in
      let uu____1035 = chk_v_u v  in
      FStar_Unionfind.puf_equivalent uu____1025 uu____1030 uu____1035
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v  ->
      let uu____1053 =
        let uu____1054 = get_univ_graph ()  in
        let uu____1059 = chk_v_u u  in
        let uu____1064 = chk_v_u v  in
        FStar_Unionfind.puf_union uu____1054 uu____1059 uu____1064  in
      set_univ_graph uu____1053
  