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
  let next_major uu____41987 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____42033 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____42033;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     })
     in
  let next_minor uu____42118 =
    let uu____42119 = FStar_ST.op_Bang major  in
    let uu____42164 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____42119;
      FStar_Syntax_Syntax.minor = uu____42164
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
    let uu____42299 = FStar_Unionfind.puf_empty ()  in
    let uu____42302 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____42299; univ_graph = uu____42302; version = v1 }
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____42312 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____42314 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____42312 uu____42314
  
let (state : uf FStar_ST.ref) =
  let uu____42331 =
    let uu____42332 = vops.next_major ()  in empty uu____42332  in
  FStar_Util.mk_ref uu____42331 
type tx =
  | TX of uf 
let (uu___is_TX : tx -> Prims.bool) = fun projectee  -> true 
let (__proj__TX__item___0 : tx -> uf) =
  fun projectee  -> match projectee with | TX _0 -> _0 
let (get : unit -> uf) = fun uu____42358  -> FStar_ST.op_Bang state 
let (set : uf -> unit) = fun u  -> FStar_ST.op_Colon_Equals state u 
let (reset : unit -> unit) =
  fun uu____42408  ->
    let v1 = vops.next_major ()  in
    let uu____42410 = empty v1  in set uu____42410
  
let (new_transaction : unit -> tx) =
  fun uu____42416  ->
    let tx = let uu____42418 = get ()  in TX uu____42418  in
    (let uu____42420 =
       let uu___425_42421 = get ()  in
       let uu____42422 = vops.next_minor ()  in
       {
         term_graph = (uu___425_42421.term_graph);
         univ_graph = (uu___425_42421.univ_graph);
         version = uu____42422
       }  in
     set uu____42420);
    tx
  
let (commit : tx -> unit) = fun tx  -> () 
let (rollback : tx -> unit) =
  fun uu____42434  -> match uu____42434 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let (get_term_graph : unit -> tgraph) =
  fun uu____42496  -> let uu____42497 = get ()  in uu____42497.term_graph 
let (get_version : unit -> FStar_Syntax_Syntax.version) =
  fun uu____42503  -> let uu____42504 = get ()  in uu____42504.version 
let (set_term_graph : tgraph -> unit) =
  fun tg  ->
    let uu____42511 =
      let uu___438_42512 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___438_42512.univ_graph);
        version = (uu___438_42512.version)
      }  in
    set uu____42511
  
let chk_v :
  'Auu____42518 .
    ('Auu____42518 * FStar_Syntax_Syntax.version) -> 'Auu____42518
  =
  fun uu____42527  ->
    match uu____42527 with
    | (u,v1) ->
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____42539 =
             let uu____42541 = version_to_string expected  in
             let uu____42543 = version_to_string v1  in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____42541 uu____42543
              in
           failwith uu____42539)
  
let (uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int) =
  fun u  ->
    let uu____42553 = get_term_graph ()  in
    let uu____42558 = chk_v u  in
    FStar_Unionfind.puf_id uu____42553 uu____42558
  
let (from_id : Prims.int -> FStar_Syntax_Syntax.uvar) =
  fun n1  ->
    let uu____42579 =
      let uu____42586 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____42586 n1  in
    let uu____42593 = get_version ()  in (uu____42579, uu____42593)
  
let (fresh : unit -> FStar_Syntax_Syntax.uvar) =
  fun uu____42605  ->
    let uu____42606 =
      let uu____42613 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____42613 FStar_Pervasives_Native.None  in
    let uu____42620 = get_version ()  in (uu____42606, uu____42620)
  
let (find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____42635 = get_term_graph ()  in
    let uu____42640 = chk_v u  in
    FStar_Unionfind.puf_find uu____42635 uu____42640
  
let (change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit) =
  fun u  ->
    fun t  ->
      let uu____42664 =
        let uu____42665 = get_term_graph ()  in
        let uu____42670 = chk_v u  in
        FStar_Unionfind.puf_change uu____42665 uu____42670
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____42664
  
let (equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool) =
  fun u  ->
    fun v1  ->
      let uu____42695 = get_term_graph ()  in
      let uu____42700 = chk_v u  in
      let uu____42711 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____42695 uu____42700 uu____42711
  
let (union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit) =
  fun u  ->
    fun v1  ->
      let uu____42735 =
        let uu____42736 = get_term_graph ()  in
        let uu____42741 = chk_v u  in
        let uu____42752 = chk_v v1  in
        FStar_Unionfind.puf_union uu____42736 uu____42741 uu____42752  in
      set_term_graph uu____42735
  
let (get_univ_graph : unit -> ugraph) =
  fun uu____42770  -> let uu____42771 = get ()  in uu____42771.univ_graph 
let (set_univ_graph : ugraph -> unit) =
  fun ug  ->
    let uu____42778 =
      let uu___457_42779 = get ()  in
      {
        term_graph = (uu___457_42779.term_graph);
        univ_graph = ug;
        version = (uu___457_42779.version)
      }  in
    set uu____42778
  
let (univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int) =
  fun u  ->
    let uu____42787 = get_univ_graph ()  in
    let uu____42792 = chk_v u  in
    FStar_Unionfind.puf_id uu____42787 uu____42792
  
let (univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar) =
  fun n1  ->
    let uu____42811 =
      let uu____42816 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____42816 n1  in
    let uu____42823 = get_version ()  in (uu____42811, uu____42823)
  
let (univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar) =
  fun uu____42833  ->
    let uu____42834 =
      let uu____42839 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____42839 FStar_Pervasives_Native.None  in
    let uu____42846 = get_version ()  in (uu____42834, uu____42846)
  
let (univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    let uu____42859 = get_univ_graph ()  in
    let uu____42864 = chk_v u  in
    FStar_Unionfind.puf_find uu____42859 uu____42864
  
let (univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit)
  =
  fun u  ->
    fun t  ->
      let uu____42886 =
        let uu____42887 = get_univ_graph ()  in
        let uu____42892 = chk_v u  in
        FStar_Unionfind.puf_change uu____42887 uu____42892
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____42886
  
let (univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool)
  =
  fun u  ->
    fun v1  ->
      let uu____42915 = get_univ_graph ()  in
      let uu____42920 = chk_v u  in
      let uu____42929 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____42915 uu____42920 uu____42929
  
let (univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit)
  =
  fun u  ->
    fun v1  ->
      let uu____42951 =
        let uu____42952 = get_univ_graph ()  in
        let uu____42957 = chk_v u  in
        let uu____42966 = chk_v v1  in
        FStar_Unionfind.puf_union uu____42952 uu____42957 uu____42966  in
      set_univ_graph uu____42951
  