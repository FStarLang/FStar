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
  let major = FStar_Util.mk_ref (Prims.parse_int "0")  in
  let minor = FStar_Util.mk_ref (Prims.parse_int "0")  in
  let next_major uu____42056 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____42102 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____42102;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     })
     in
  let next_minor uu____42187 =
    let uu____42188 = FStar_ST.op_Bang major  in
    let uu____42233 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____42188;
      FStar_Syntax_Syntax.minor = uu____42233
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
  version: FStar_Syntax_Syntax.version }
let (__proj__Mkuf__item__term_graph : uf -> tgraph) =
  fun projectee  ->
    match projectee with | { term_graph; univ_graph; version;_} -> term_graph
  
let (__proj__Mkuf__item__univ_graph : uf -> ugraph) =
  fun projectee  ->
    match projectee with | { term_graph; univ_graph; version;_} -> univ_graph
  
let (__proj__Mkuf__item__version : uf -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with | { term_graph; univ_graph; version;_} -> version
  
let (empty : FStar_Syntax_Syntax.version -> uf) =
  fun v1  ->
    let uu____42368 = FStar_Unionfind.puf_empty ()  in
    let uu____42371 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____42368; univ_graph = uu____42371; version = v1 }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____42381 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____42383 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____42381 uu____42383
  
let (state : uf FStar_ST.ref) =
  let uu____42400 =
    let uu____42401 = vops.next_major ()  in empty uu____42401  in
  FStar_Util.mk_ref uu____42400 
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____42427  -> FStar_ST.op_Bang state 
let (set : uf -> unit) = fun u  -> FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____42477  ->
    let v1 = vops.next_major ()  in
    let uu____42479 = empty v1  in set uu____42479
  
let (new_transaction : unit -> tx) =
  fun uu____42485  ->
    let tx = let uu____42487 = get ()  in TX uu____42487  in
    (let uu____42489 =
       let uu___425_42490 = get ()  in
       let uu____42491 = vops.next_minor ()  in
       {
         term_graph = (uu___425_42490.term_graph);
         univ_graph = (uu___425_42490.univ_graph);
         version = uu____42491
       }  in
     set uu____42489);
    tx
  
let (commit : tx -> unit) = fun tx  -> () 
let (rollback : tx -> unit) =
  fun uu____42503  -> match uu____42503 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____42565  -> let uu____42566 = get ()  in uu____42566.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____42572  -> let uu____42573 = get ()  in uu____42573.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____42580 =
      let uu___438_42581 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___438_42581.univ_graph);
        version = (uu___438_42581.version)
      }  in
    set uu____42580
  
let chk_v :
  'Auu____42587 .
    ('Auu____42587 * FStar_Syntax_Syntax.version) -> 'Auu____42587
  =
  fun uu____42596  ->
    match uu____42596 with
    | (u,v1) ->
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____42608 =
             let uu____42610 = version_to_string expected  in
             let uu____42612 = version_to_string v1  in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____42610 uu____42612
              in
           failwith uu____42608)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____42622 = get_term_graph ()  in
    let uu____42627 = chk_v u  in
    FStar_Unionfind.puf_id uu____42622 uu____42627
  
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1  ->
    let uu____42648 =
      let uu____42655 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____42655 n1  in
    let uu____42662 = get_version ()  in (uu____42648, uu____42662)
  
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____42674  ->
    let uu____42675 =
      let uu____42682 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____42682 FStar_Pervasives_Native.None  in
    let uu____42689 = get_version ()  in (uu____42675, uu____42689)
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____42704 = get_term_graph ()  in
    let uu____42709 = chk_v u  in
    FStar_Unionfind.puf_find uu____42704 uu____42709
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____42733 =
        let uu____42734 = get_term_graph ()  in
        let uu____42739 = chk_v u  in
        FStar_Unionfind.puf_change uu____42734 uu____42739
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____42733
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v1  ->
      let uu____42764 = get_term_graph ()  in
      let uu____42769 = chk_v u  in
      let uu____42780 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____42764 uu____42769 uu____42780
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v1  ->
      let uu____42804 =
        let uu____42805 = get_term_graph ()  in
        let uu____42810 = chk_v u  in
        let uu____42821 = chk_v v1  in
        FStar_Unionfind.puf_union uu____42805 uu____42810 uu____42821  in
      set_term_graph uu____42804
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____42839  -> let uu____42840 = get ()  in uu____42840.univ_graph 
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____42847 =
      let uu___457_42848 = get ()  in
      {
        term_graph = (uu___457_42848.term_graph);
        univ_graph = ug;
        version = (uu___457_42848.version)
      }  in
    set uu____42847
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____42856 = get_univ_graph ()  in
    let uu____42861 = chk_v u  in
    FStar_Unionfind.puf_id uu____42856 uu____42861
  
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1  ->
    let uu____42880 =
      let uu____42885 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____42885 n1  in
    let uu____42892 = get_version ()  in (uu____42880, uu____42892)
  
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____42902  ->
    let uu____42903 =
      let uu____42908 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____42908 FStar_Pervasives_Native.None  in
    let uu____42915 = get_version ()  in (uu____42903, uu____42915)
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____42928 = get_univ_graph ()  in
    let uu____42933 = chk_v u  in
    FStar_Unionfind.puf_find uu____42928 uu____42933
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____42955 =
        let uu____42956 = get_univ_graph ()  in
        let uu____42961 = chk_v u  in
        FStar_Unionfind.puf_change uu____42956 uu____42961
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____42955
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v1  ->
      let uu____42984 = get_univ_graph ()  in
      let uu____42989 = chk_v u  in
      let uu____42998 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____42984 uu____42989 uu____42998
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v1  ->
      let uu____43020 =
        let uu____43021 = get_univ_graph ()  in
        let uu____43026 = chk_v u  in
        let uu____43035 = chk_v v1  in
        FStar_Unionfind.puf_union uu____43021 uu____43026 uu____43035  in
      set_univ_graph uu____43020
  