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
  let next_major uu____42061 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____42107 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____42107;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     })
     in
  let next_minor uu____42192 =
    let uu____42193 = FStar_ST.op_Bang major  in
    let uu____42238 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____42193;
      FStar_Syntax_Syntax.minor = uu____42238
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
    let uu____42373 = FStar_Unionfind.puf_empty ()  in
    let uu____42376 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____42373; univ_graph = uu____42376; version = v1 }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____42386 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____42388 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____42386 uu____42388
  
let (state : uf FStar_ST.ref) =
  let uu____42405 =
    let uu____42406 = vops.next_major ()  in empty uu____42406  in
  FStar_Util.mk_ref uu____42405 
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____42432  -> FStar_ST.op_Bang state 
let (set : uf -> unit) = fun u  -> FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____42482  ->
    let v1 = vops.next_major ()  in
    let uu____42484 = empty v1  in set uu____42484
  
let (new_transaction : unit -> tx) =
  fun uu____42490  ->
    let tx = let uu____42492 = get ()  in TX uu____42492  in
    (let uu____42494 =
       let uu___425_42495 = get ()  in
       let uu____42496 = vops.next_minor ()  in
       {
         term_graph = (uu___425_42495.term_graph);
         univ_graph = (uu___425_42495.univ_graph);
         version = uu____42496
       }  in
     set uu____42494);
    tx
  
let (commit : tx -> unit) = fun tx  -> () 
let (rollback : tx -> unit) =
  fun uu____42508  -> match uu____42508 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____42570  -> let uu____42571 = get ()  in uu____42571.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____42577  -> let uu____42578 = get ()  in uu____42578.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____42585 =
      let uu___438_42586 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___438_42586.univ_graph);
        version = (uu___438_42586.version)
      }  in
    set uu____42585
  
let chk_v :
  'Auu____42592 .
    ('Auu____42592 * FStar_Syntax_Syntax.version) -> 'Auu____42592
  =
  fun uu____42601  ->
    match uu____42601 with
    | (u,v1) ->
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____42613 =
             let uu____42615 = version_to_string expected  in
             let uu____42617 = version_to_string v1  in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____42615 uu____42617
              in
           failwith uu____42613)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____42627 = get_term_graph ()  in
    let uu____42632 = chk_v u  in
    FStar_Unionfind.puf_id uu____42627 uu____42632
  
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1  ->
    let uu____42653 =
      let uu____42660 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____42660 n1  in
    let uu____42667 = get_version ()  in (uu____42653, uu____42667)
  
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____42679  ->
    let uu____42680 =
      let uu____42687 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____42687 FStar_Pervasives_Native.None  in
    let uu____42694 = get_version ()  in (uu____42680, uu____42694)
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____42709 = get_term_graph ()  in
    let uu____42714 = chk_v u  in
    FStar_Unionfind.puf_find uu____42709 uu____42714
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____42738 =
        let uu____42739 = get_term_graph ()  in
        let uu____42744 = chk_v u  in
        FStar_Unionfind.puf_change uu____42739 uu____42744
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____42738
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v1  ->
      let uu____42769 = get_term_graph ()  in
      let uu____42774 = chk_v u  in
      let uu____42785 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____42769 uu____42774 uu____42785
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v1  ->
      let uu____42809 =
        let uu____42810 = get_term_graph ()  in
        let uu____42815 = chk_v u  in
        let uu____42826 = chk_v v1  in
        FStar_Unionfind.puf_union uu____42810 uu____42815 uu____42826  in
      set_term_graph uu____42809
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____42844  -> let uu____42845 = get ()  in uu____42845.univ_graph 
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____42852 =
      let uu___457_42853 = get ()  in
      {
        term_graph = (uu___457_42853.term_graph);
        univ_graph = ug;
        version = (uu___457_42853.version)
      }  in
    set uu____42852
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____42861 = get_univ_graph ()  in
    let uu____42866 = chk_v u  in
    FStar_Unionfind.puf_id uu____42861 uu____42866
  
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1  ->
    let uu____42885 =
      let uu____42890 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____42890 n1  in
    let uu____42897 = get_version ()  in (uu____42885, uu____42897)
  
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____42907  ->
    let uu____42908 =
      let uu____42913 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____42913 FStar_Pervasives_Native.None  in
    let uu____42920 = get_version ()  in (uu____42908, uu____42920)
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____42933 = get_univ_graph ()  in
    let uu____42938 = chk_v u  in
    FStar_Unionfind.puf_find uu____42933 uu____42938
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____42960 =
        let uu____42961 = get_univ_graph ()  in
        let uu____42966 = chk_v u  in
        FStar_Unionfind.puf_change uu____42961 uu____42966
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____42960
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v1  ->
      let uu____42989 = get_univ_graph ()  in
      let uu____42994 = chk_v u  in
      let uu____43003 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____42989 uu____42994 uu____43003
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v1  ->
      let uu____43025 =
        let uu____43026 = get_univ_graph ()  in
        let uu____43031 = chk_v u  in
        let uu____43040 = chk_v v1  in
        FStar_Unionfind.puf_union uu____43026 uu____43031 uu____43040  in
      set_univ_graph uu____43025
  