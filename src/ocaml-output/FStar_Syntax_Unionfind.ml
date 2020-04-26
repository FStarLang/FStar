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
      ((let uu____447 = FStar_Util.stack_dump ()  in
        FStar_Util.print_error uu____447);
       FStar_Errors.raise_error
         (FStar_Errors.Fatal_BadUvar,
           "Internal error: UF graph was in read-only mode")
         FStar_Range.dummyRange)
    else ()
  
let (set : uf -> unit) =
  fun u  -> fail_if_ro (); FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____484  ->
    fail_if_ro ();
    (let v = vops.next_major ()  in
     let uu____487 =
       let uu___66_488 = empty v  in
       {
         term_graph = (uu___66_488.term_graph);
         univ_graph = (uu___66_488.univ_graph);
         version = (uu___66_488.version);
         ro = false
       }  in
     set uu____487)
  
let (new_transaction : unit -> tx) =
  fun uu____495  ->
    let tx1 = let uu____497 = get ()  in TX uu____497  in
    (let uu____499 =
       let uu___70_500 = get ()  in
       let uu____501 = vops.next_minor ()  in
       {
         term_graph = (uu___70_500.term_graph);
         univ_graph = (uu___70_500.univ_graph);
         version = uu____501;
         ro = (uu___70_500.ro)
       }  in
     set uu____499);
    tx1
  
let (commit : tx -> unit) = fun tx1  -> () 
let (rollback : tx -> unit) =
  fun uu____513  -> match uu____513 with | TX uf1 -> set uf1 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____542  -> let uu____543 = get ()  in uu____543.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____549  -> let uu____550 = get ()  in uu____550.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____557 =
      let uu___83_558 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___83_558.univ_graph);
        version = (uu___83_558.version);
        ro = (uu___83_558.ro)
      }  in
    set uu____557
  
let (chk_v_t :
  (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version * FStar_Range.range)
    ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
      FStar_Unionfind.p_uvar)
  =
  fun uu____578  ->
    match uu____578 with
    | (u,v,rng) ->
        let uvar_to_string u1 =
          let uu____619 =
            let uu____621 =
              let uu____623 = get_term_graph ()  in
              FStar_Unionfind.puf_id uu____623 u1  in
            FStar_All.pipe_right uu____621 FStar_Util.string_of_int  in
          Prims.op_Hat "?" uu____619  in
        let expected = get_version ()  in
        if
          (v.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____642 =
             let uu____648 =
               let uu____650 = uvar_to_string u  in
               let uu____652 = version_to_string expected  in
               let uu____654 = version_to_string v  in
               FStar_Util.format3
                 "Internal error: incompatible version for term unification variable %s: current version is %s; got version %s"
                 uu____650 uu____652 uu____654
                in
             (FStar_Errors.Fatal_BadUvar, uu____648)  in
           FStar_Errors.raise_error uu____642 rng)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____669 = get_term_graph ()  in
    let uu____674 = chk_v_t u  in FStar_Unionfind.puf_id uu____669 uu____674
  
let (fresh : FStar_Range.range -> FStar_Syntax_Syntax.uvar) =
  fun rng  ->
    fail_if_ro ();
    (let uu____688 =
       let uu____695 = get_term_graph ()  in
       FStar_Unionfind.puf_fresh uu____695 FStar_Pervasives_Native.None  in
     let uu____702 = get_version ()  in (uu____688, uu____702, rng))
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____717 = get_term_graph ()  in
    let uu____722 = chk_v_t u  in
    FStar_Unionfind.puf_find uu____717 uu____722
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____740 =
        let uu____741 = get_term_graph ()  in
        let uu____746 = chk_v_t u  in
        FStar_Unionfind.puf_change uu____741 uu____746
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____740
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v  ->
      let uu____765 = get_term_graph ()  in
      let uu____770 = chk_v_t u  in
      let uu____775 = chk_v_t v  in
      FStar_Unionfind.puf_equivalent uu____765 uu____770 uu____775
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v  ->
      let uu____793 =
        let uu____794 = get_term_graph ()  in
        let uu____799 = chk_v_t u  in
        let uu____804 = chk_v_t v  in
        FStar_Unionfind.puf_union uu____794 uu____799 uu____804  in
      set_term_graph uu____793
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____816  -> let uu____817 = get ()  in uu____817.univ_graph 
let (chk_v_u :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version * FStar_Range.range)
    ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
      FStar_Unionfind.p_uvar)
  =
  fun uu____837  ->
    match uu____837 with
    | (u,v,rng) ->
        let uvar_to_string u1 =
          let uu____878 =
            let uu____880 =
              let uu____882 = get_univ_graph ()  in
              FStar_Unionfind.puf_id uu____882 u1  in
            FStar_All.pipe_right uu____880 FStar_Util.string_of_int  in
          Prims.op_Hat "?" uu____878  in
        let expected = get_version ()  in
        if
          (v.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____901 =
             let uu____907 =
               let uu____909 = uvar_to_string u  in
               let uu____911 = version_to_string expected  in
               let uu____913 = version_to_string v  in
               FStar_Util.format3
                 "Internal error: incompatible version for universe unification variable %s: current version is %s; got version %s"
                 uu____909 uu____911 uu____913
                in
             (FStar_Errors.Fatal_BadUvar, uu____907)  in
           FStar_Errors.raise_error uu____901 rng)
  
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____927 =
      let uu___113_928 = get ()  in
      {
        term_graph = (uu___113_928.term_graph);
        univ_graph = ug;
        version = (uu___113_928.version);
        ro = (uu___113_928.ro)
      }  in
    set uu____927
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____936 = get_univ_graph ()  in
    let uu____941 = chk_v_u u  in FStar_Unionfind.puf_id uu____936 uu____941
  
let (univ_fresh : FStar_Range.range -> FStar_Syntax_Syntax.universe_uvar) =
  fun rng  ->
    fail_if_ro ();
    (let uu____955 =
       let uu____960 = get_univ_graph ()  in
       FStar_Unionfind.puf_fresh uu____960 FStar_Pervasives_Native.None  in
     let uu____967 = get_version ()  in (uu____955, uu____967, rng))
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____980 = get_univ_graph ()  in
    let uu____985 = chk_v_u u  in
    FStar_Unionfind.puf_find uu____980 uu____985
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____1003 =
        let uu____1004 = get_univ_graph ()  in
        let uu____1009 = chk_v_u u  in
        FStar_Unionfind.puf_change uu____1004 uu____1009
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____1003
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v  ->
      let uu____1028 = get_univ_graph ()  in
      let uu____1033 = chk_v_u u  in
      let uu____1038 = chk_v_u v  in
      FStar_Unionfind.puf_equivalent uu____1028 uu____1033 uu____1038
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v  ->
      let uu____1056 =
        let uu____1057 = get_univ_graph ()  in
        let uu____1062 = chk_v_u u  in
        let uu____1067 = chk_v_u v  in
        FStar_Unionfind.puf_union uu____1057 uu____1062 uu____1067  in
      set_univ_graph uu____1056
  