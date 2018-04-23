open Prims
type vops_t =
  {
  next_major: unit -> FStar_Syntax_Syntax.version ;
  next_minor: unit -> FStar_Syntax_Syntax.version }[@@deriving show]
let __proj__Mkvops_t__item__next_major :
  vops_t -> unit -> FStar_Syntax_Syntax.version =
  fun projectee  ->
    match projectee with
    | { next_major = __fname__next_major; next_minor = __fname__next_minor;_}
        -> __fname__next_major
  
let __proj__Mkvops_t__item__next_minor :
  vops_t -> unit -> FStar_Syntax_Syntax.version =
  fun projectee  ->
    match projectee with
    | { next_major = __fname__next_major; next_minor = __fname__next_minor;_}
        -> __fname__next_minor
  
let vops : vops_t =
  let major = FStar_Util.mk_ref (Prims.lift_native_int (0))  in
  let minor = FStar_Util.mk_ref (Prims.lift_native_int (0))  in
  let next_major uu____72 =
    FStar_ST.op_Colon_Equals minor (Prims.lift_native_int (0));
    (let uu____119 = FStar_Util.incr major; FStar_ST.op_Bang major  in
     {
       FStar_Syntax_Syntax.major = uu____119;
       FStar_Syntax_Syntax.minor = (Prims.lift_native_int (0))
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
    let uu____383 = FStar_Unionfind.puf_empty ()  in
    let uu____386 = FStar_Unionfind.puf_empty ()  in
    { term_graph = uu____383; univ_graph = uu____386; version = v1 }
  
let version_to_string : FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____394 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____395 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____394 uu____395
  
let state : uf FStar_ST.ref =
  let uu____409 = let uu____410 = vops.next_major ()  in empty uu____410  in
  FStar_Util.mk_ref uu____409 
type tx =
  | TX of uf [@@deriving show]
let uu___is_TX : tx -> Prims.bool = fun projectee  -> true 
let __proj__TX__item___0 : tx -> uf =
  fun projectee  -> match projectee with | TX _0 -> _0 
let get : unit -> uf = fun uu____431  -> FStar_ST.op_Bang state 
let set : uf -> unit = fun u  -> FStar_ST.op_Colon_Equals state u 
let reset : unit -> unit =
  fun uu____487  ->
    let v1 = vops.next_major ()  in
    let uu____489 = empty v1  in set uu____489
  
let new_transaction : unit -> tx =
  fun uu____494  ->
    let tx = let uu____496 = get ()  in TX uu____496  in
    (let uu____498 =
       let uu___25_499 = get ()  in
       let uu____500 = vops.next_minor ()  in
       {
         term_graph = (uu___25_499.term_graph);
         univ_graph = (uu___25_499.univ_graph);
         version = uu____500
       }  in
     set uu____498);
    tx
  
let commit : tx -> unit = fun tx  -> () 
let rollback : tx -> unit =
  fun uu____510  -> match uu____510 with | TX uf -> set uf 
let update_in_tx : 'a . 'a FStar_ST.ref -> 'a -> unit =
  fun r  -> fun x  -> () 
let get_term_graph : unit -> tgraph =
  fun uu____570  -> let uu____571 = get ()  in uu____571.term_graph 
let get_version : unit -> FStar_Syntax_Syntax.version =
  fun uu____576  -> let uu____577 = get ()  in uu____577.version 
let set_term_graph : tgraph -> unit =
  fun tg  ->
    let uu____583 =
      let uu___26_584 = get ()  in
      {
        term_graph = tg;
        univ_graph = (uu___26_584.univ_graph);
        version = (uu___26_584.version)
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
  
let uvar_id : FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____615 = get_term_graph ()  in
    let uu____620 = chk_v u  in FStar_Unionfind.puf_id uu____615 uu____620
  
let from_id : Prims.int -> FStar_Syntax_Syntax.uvar =
  fun n1  ->
    let uu____638 =
      let uu____643 = get_term_graph ()  in
      FStar_Unionfind.puf_fromid uu____643 n1  in
    let uu____650 = get_version ()  in (uu____638, uu____650)
  
let fresh : unit -> FStar_Syntax_Syntax.uvar =
  fun uu____659  ->
    let uu____660 =
      let uu____665 = get_term_graph ()  in
      FStar_Unionfind.puf_fresh uu____665 FStar_Pervasives_Native.None  in
    let uu____672 = get_version ()  in (uu____660, uu____672)
  
let find :
  FStar_Syntax_Syntax.uvar ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____684 = get_term_graph ()  in
    let uu____689 = chk_v u  in FStar_Unionfind.puf_find uu____684 uu____689
  
let change : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit =
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
      let uu____741 = get_term_graph ()  in
      let uu____746 = chk_v u  in
      let uu____757 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____741 uu____746 uu____757
  
let union : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> unit =
  fun u  ->
    fun v1  ->
      let uu____780 =
        let uu____781 = get_term_graph ()  in
        let uu____786 = chk_v u  in
        let uu____797 = chk_v v1  in
        FStar_Unionfind.puf_union uu____781 uu____786 uu____797  in
      set_term_graph uu____780
  
let get_univ_graph : unit -> ugraph =
  fun uu____814  -> let uu____815 = get ()  in uu____815.univ_graph 
let set_univ_graph : ugraph -> unit =
  fun ug  ->
    let uu____821 =
      let uu___27_822 = get ()  in
      {
        term_graph = (uu___27_822.term_graph);
        univ_graph = ug;
        version = (uu___27_822.version)
      }  in
    set uu____821
  
let univ_uvar_id : FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____828 = get_univ_graph ()  in
    let uu____833 = chk_v u  in FStar_Unionfind.puf_id uu____828 uu____833
  
let univ_from_id : Prims.int -> FStar_Syntax_Syntax.universe_uvar =
  fun n1  ->
    let uu____849 =
      let uu____854 = get_univ_graph ()  in
      FStar_Unionfind.puf_fromid uu____854 n1  in
    let uu____861 = get_version ()  in (uu____849, uu____861)
  
let univ_fresh : unit -> FStar_Syntax_Syntax.universe_uvar =
  fun uu____870  ->
    let uu____871 =
      let uu____876 = get_univ_graph ()  in
      FStar_Unionfind.puf_fresh uu____876 FStar_Pervasives_Native.None  in
    let uu____883 = get_version ()  in (uu____871, uu____883)
  
let univ_find :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun u  ->
    let uu____895 = get_univ_graph ()  in
    let uu____900 = chk_v u  in FStar_Unionfind.puf_find uu____895 uu____900
  
let univ_change :
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe -> unit =
  fun u  ->
    fun t  ->
      let uu____921 =
        let uu____922 = get_univ_graph ()  in
        let uu____927 = chk_v u  in
        FStar_Unionfind.puf_change uu____922 uu____927
          (FStar_Pervasives_Native.Some t)
         in
      set_univ_graph uu____921
  
let univ_equiv :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
      let uu____948 = get_univ_graph ()  in
      let uu____953 = chk_v u  in
      let uu____962 = chk_v v1  in
      FStar_Unionfind.puf_equivalent uu____948 uu____953 uu____962
  
let univ_union :
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> unit
  =
  fun u  ->
    fun v1  ->
      let uu____983 =
        let uu____984 = get_univ_graph ()  in
        let uu____989 = chk_v u  in
        let uu____998 = chk_v v1  in
        FStar_Unionfind.puf_union uu____984 uu____989 uu____998  in
      set_univ_graph uu____983
  