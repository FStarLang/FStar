open Prims
type vops_t =
  {
  next_major: Prims.unit -> FStar_Syntax_Syntax.version ;
  next_minor: Prims.unit -> FStar_Syntax_Syntax.version }[@@deriving show]
let __proj__Mkvops_t__item__next_major :
  vops_t -> Prims.unit -> FStar_Syntax_Syntax.version =
  fun projectee  ->
    match projectee with
    | { next_major = __fname__next_major; next_minor = __fname__next_minor;_}
        -> __fname__next_major
  
let __proj__Mkvops_t__item__next_minor :
  vops_t -> Prims.unit -> FStar_Syntax_Syntax.version =
  fun projectee  ->
    match projectee with
    | { next_major = __fname__next_major; next_minor = __fname__next_minor;_}
        -> __fname__next_minor
  
let vops : vops_t =
  let major = FStar_Util.mk_ref (Prims.parse_int "0")  in
  let minor = FStar_Util.mk_ref (Prims.parse_int "0")  in
  let next_major uu____52 =
    FStar_ST.op_Colon_Equals minor (Prims.parse_int "0");
    (let uu____116 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____116;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     })
     in
  let next_minor uu____204 =
    let uu____205 = FStar_ST.op_Bang major  in
    let uu____268 = FStar_Util.incr minor; FStar_ST.op_Bang minor  in
    {
      FStar_Syntax_Syntax.major = uu____205;
      FStar_Syntax_Syntax.minor = uu____268
    }  in
  { next_major; next_minor } 
type tgraph =
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option FStar_Unionfind.puf
[@@deriving show]
type ugraph =
  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.puf[@@deriving show]
type uf =
  {
  term_graph: tgraph ;
  univ_graph: ugraph ;
  version: FStar_Syntax_Syntax.version }[@@deriving show]
let __proj__Mkuf__item__term_graph : uf -> tgraph =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__term_graph
  
let __proj__Mkuf__item__univ_graph : uf -> ugraph =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__univ_graph
  
let __proj__Mkuf__item__version : uf -> FStar_Syntax_Syntax.version =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;
        version = __fname__version;_} -> __fname__version
  
let empty : FStar_Syntax_Syntax.version -> uf =
  fun v1  ->
    let uu____394 = FStar_Unionfind.puf_empty ()  in
    let uu____397 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____394; univ_graph = uu____397; version = v1 }
  
let version_to_string : FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____403 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____404 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____403 uu____404
  
let state : uf FStar_ST.ref =
  let uu____414 = let uu____415 = vops.next_major ()  in empty uu____415  in
  FStar_Util.mk_ref uu____414 
type tx =
  | TX of uf [@@deriving show]
let uu___is_TX : tx -> Prims.bool = fun projectee  -> true 
let __proj__TX__item___0 : tx -> uf =
  fun projectee  -> match projectee with | TX _0 -> _0 
let get : Prims.unit -> uf = fun uu____429  -> FStar_ST.op_Bang state 
let set : uf -> Prims.unit = fun u  -> FStar_ST.op_Colon_Equals state u 
let reset : Prims.unit -> Prims.unit =
  fun uu____531  ->
    let v1 = vops.next_major ()  in
    let uu____533 = empty v1  in set uu____533
  
let new_transaction : Prims.unit -> tx =
  fun uu____536  ->
    let tx = let uu____538 = get ()  in TX uu____538  in
    (let uu____540 =
       let uu___42_541 = get ()  in
       let uu____542 = vops.next_minor ()  in
       {
         term_graph = (uu___42_541.term_graph);
         univ_graph = (uu___42_541.univ_graph);
         version = uu____542
       }  in
     set uu____540);
    tx
  
let commit : tx -> Prims.unit = fun tx  -> () 
let rollback : tx -> Prims.unit =
  fun uu____548  -> match uu____548 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> Prims.unit =
  fun r  -> fun x  -> () 
let get_term_graph : Prims.unit -> tgraph =
  fun uu____589  -> let uu____590 = get ()  in uu____590.term_graph 
let get_version : Prims.unit -> FStar_Syntax_Syntax.version =
  fun uu____593  -> let uu____594 = get ()  in uu____594.version 
let set_term_graph : tgraph -> Prims.unit =
  fun tg  ->
    let uu____598 =
      let uu___43_599 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___43_599.univ_graph);
        version = (uu___43_599.version)
      }  in
    set uu____598
  
let chk_v :
  'Auu____602 .
    ('Auu____602,FStar_Syntax_Syntax.version) FStar_Pervasives_Native.tuple2
      -> 'Auu____602
  =
  fun uu____610  ->
    match uu____610 with
    | (u,v1) ->
        let expected = get_version ()  in
        if
          (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
            &&
            (v1.FStar_Syntax_Syntax.minor <=
               expected.FStar_Syntax_Syntax.minor)
        then u
        else
          (let uu____619 =
             let uu____620 = version_to_string expected  in
             let uu____621 = version_to_string v1  in
             FStar_Util.format2
               "Incompatible version for unification variable: current version is %s; got version %s"
               uu____620 uu____621
              in
           failwith uu____619)
  
let uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____625 = get_term_graph ()  in
    let uu____630 = chk_v u  in FStar_Unionfind.puf_id uu____625 uu____630
  
let from_id : Prims.int -> FStar_Syntax_Syntax.uvar =
  fun n1  ->
    let uu____646 =
      let uu____651 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____651 n1  in
    let uu____658 = get_version ()  in (uu____646, uu____658)
  
let fresh : Prims.unit -> FStar_Syntax_Syntax.uvar =
  fun uu____665  ->
    let uu____666 =
      let uu____671 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____671 FStar_Pervasives_Native.None  in
    let uu____678 = get_version ()  in (uu____666, uu____678)
  
let find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____688 = get_term_graph ()  in
    let uu____693 = chk_v u  in FStar_Unionfind.puf_find uu____688 uu____693
  
let change :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
      let uu____712 =
        let uu____713 = get_term_graph ()  in
        let uu____718 = chk_v u  in
        FStar_Unionfind.puf_change uu____713 uu____718
          (FStar_Pervasives_Native.Some t)
         in
      set_term_graph uu____712
  
let equiv :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool =
  fun u  ->
    fun v1  ->
      let uu____737 = get_term_graph ()  in
      let uu____742 = chk_v u  in
      let uu____753 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____737 uu____742 uu____753
  
let union :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit =
  fun u  ->
    fun v1  ->
      let uu____772 =
        let uu____773 = get_term_graph ()  in
        let uu____778 = chk_v u  in
        let uu____789 = chk_v v1  in
        FStar_Unionfind.puf_union uu____773 uu____778 uu____789  in
      set_term_graph uu____772
  
let get_univ_graph : Prims.unit -> ugraph =
  fun uu____804  -> let uu____805 = get ()  in uu____805.univ_graph 
let set_univ_graph : ugraph -> Prims.unit =
  fun ug  ->
    let uu____809 =
      let uu___44_810 = get ()  in
      {
        term_graph = (uu___44_810.term_graph);
        univ_graph = ug;
        version = (uu___44_810.version)
      }  in
    set uu____809
  
let univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____814 = get_univ_graph ()  in
    let uu____819 = chk_v u  in FStar_Unionfind.puf_id uu____814 uu____819
  
let univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar =
  fun n1  ->
    let uu____833 =
      let uu____838 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____838 n1  in
    let uu____845 = get_version ()  in (uu____833, uu____845)
  
let univ_fresh : Prims.unit -> FStar_Syntax_Syntax.universe_uvar =
  fun uu____852  ->
    let uu____853 =
      let uu____858 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____858 FStar_Pervasives_Native.None  in
    let uu____865 = get_version ()  in (uu____853, uu____865)
  
let univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____875 = get_univ_graph ()  in
    let uu____880 = chk_v u  in FStar_Unionfind.puf_find uu____875 uu____880
  
let univ_change :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
      let uu____897 =
        let uu____898 = get_univ_graph ()  in
        let uu____903 = chk_v u  in
        FStar_Unionfind.puf_change uu____898 uu____903
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____897
  
let univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____920 = get_univ_graph ()  in
      let uu____925 = chk_v u  in
      let uu____934 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____920 uu____925 uu____934
  
let univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
      let uu____951 =
        let uu____952 = get_univ_graph ()  in
        let uu____957 = chk_v u  in
        let uu____966 = chk_v v1  in
        FStar_Unionfind.puf_union uu____952 uu____957 uu____966  in
      set_univ_graph uu____951
  