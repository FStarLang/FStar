open Prims
type vops_t =
  {
  next_major: unit -> FStar_Syntax_Syntax.version ;
  next_minor: unit -> FStar_Syntax_Syntax.version }
let (__proj__Mkvops_t__item__next_major :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with
    | { next_major = __fname__next_major; next_minor = __fname__next_minor;_}
        -> __fname__next_major
  
let (__proj__Mkvops_t__item__next_minor :
  vops_t -> unit -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with
    | { next_major = __fname__next_major; next_minor = __fname__next_minor;_}
        -> __fname__next_minor
  
let (vops : vops_t) =
  let major = FStar_Util.mk_ref (Prims.parse_int "0")  in
  let minor = FStar_Util.mk_ref (Prims.parse_int "0")  in
  let next_major uu____72 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____119 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____119;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     })
     in
  let next_minor uu____204 =
    let uu____205 = FStar_ST.op_Bang major  in
    let uu____251 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____205;
      FStar_Syntax_Syntax.minor = uu____251
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
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__term_graph
  
let (__proj__Mkuf__item__univ_graph : uf -> ugraph) =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__univ_graph
  
let (__proj__Mkuf__item__version : uf -> FStar_Syntax_Syntax.version) =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__version
  
let (empty : FStar_Syntax_Syntax.version -> uf) =
  fun v1  ->
    let uu____383 = FStar_Unionfind.puf_empty ()  in
    let uu____386 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____383; univ_graph = uu____386; version = v1 }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____394 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____395 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____394 uu____395
  
let (state : uf FStar_ST.ref) =
  let uu____409 = let uu____410 = vops.next_major ()  in empty uu____410  in
  FStar_Util.mk_ref uu____409 
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____431  -> FStar_ST.op_Bang state 
let (set : uf -> unit) = fun u  -> FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____487  ->
    let v1 = vops.next_major ()  in
    let uu____489 = empty v1  in set uu____489
  
let (new_transaction : unit -> tx) =
  fun uu____494  ->
    let tx = let uu____496 = get ()  in TX uu____496  in
    (let uu____498 =
       let uu___82_499 = get ()  in
       let uu____500 = vops.next_minor ()  in
       {
         term_graph = (uu___82_499.term_graph);
         univ_graph = (uu___82_499.univ_graph);
         version = uu____500
       }  in
     set uu____498);
    tx
  
let (commit : tx -> unit) = fun tx  -> () 
let (rollback : tx -> unit) =
  fun uu____510  -> match uu____510 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____570  -> let uu____571 = get ()  in uu____571.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____576  -> let uu____577 = get ()  in uu____577.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____583 =
      let uu___83_584 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___83_584.univ_graph);
        version = (uu___83_584.version)
      }  in
    set uu____583
  
let chk_v :
  'Auu____589 .
    ('Auu____589,FStar_Syntax_Syntax.version) FStar_Pervasives_Native.tuple2
      -> 'Auu____589
  =
  fun uu____598  ->
    match uu____598 with
    | (u,v1) ->
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____607 =
             let uu____608 = version_to_string expected  in
             let uu____609 = version_to_string v1  in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____608 uu____609
              in
           failwith uu____607)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____615 = get_term_graph ()  in
    let uu____620 = chk_v u  in FStar_Unionfind.puf_id uu____615 uu____620
  
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1  ->
    let uu____638 =
      let uu____645 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____645 n1  in
    let uu____652 = get_version ()  in (uu____638, uu____652)
  
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____663  ->
    let uu____664 =
      let uu____671 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____671 FStar_Pervasives_Native.None  in
    let uu____678 = get_version ()  in (uu____664, uu____678)
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____692 = get_term_graph ()  in
    let uu____697 = chk_v u  in FStar_Unionfind.puf_find uu____692 uu____697
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____720 =
        let uu____721 = get_term_graph ()  in
        let uu____726 = chk_v u  in
        FStar_Unionfind.puf_change uu____721 uu____726
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____720
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v1  ->
      let uu____749 = get_term_graph ()  in
      let uu____754 = chk_v u  in
      let uu____765 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____749 uu____754 uu____765
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v1  ->
      let uu____788 =
        let uu____789 = get_term_graph ()  in
        let uu____794 = chk_v u  in
        let uu____805 = chk_v v1  in
        FStar_Unionfind.puf_union uu____789 uu____794 uu____805  in
      set_term_graph uu____788
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____822  -> let uu____823 = get ()  in uu____823.univ_graph 
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____829 =
      let uu___84_830 = get ()  in
      {
        term_graph = (uu___84_830.term_graph);
        univ_graph = ug;
        version = (uu___84_830.version)
      }  in
    set uu____829
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____836 = get_univ_graph ()  in
    let uu____841 = chk_v u  in FStar_Unionfind.puf_id uu____836 uu____841
  
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1  ->
    let uu____857 =
      let uu____862 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____862 n1  in
    let uu____869 = get_version ()  in (uu____857, uu____869)
  
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____878  ->
    let uu____879 =
      let uu____884 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____884 FStar_Pervasives_Native.None  in
    let uu____891 = get_version ()  in (uu____879, uu____891)
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____903 = get_univ_graph ()  in
    let uu____908 = chk_v u  in FStar_Unionfind.puf_find uu____903 uu____908
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____929 =
        let uu____930 = get_univ_graph ()  in
        let uu____935 = chk_v u  in
        FStar_Unionfind.puf_change uu____930 uu____935
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____929
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v1  ->
      let uu____956 = get_univ_graph ()  in
      let uu____961 = chk_v u  in
      let uu____970 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____956 uu____961 uu____970
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v1  ->
      let uu____991 =
        let uu____992 = get_univ_graph ()  in
        let uu____997 = chk_v u  in
        let uu____1006 = chk_v v1  in
        FStar_Unionfind.puf_union uu____992 uu____997 uu____1006  in
      set_univ_graph uu____991
  