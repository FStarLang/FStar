open Prims
type vops_t =
  {
  next_major: Prims.unit -> FStar_Syntax_Syntax.version;
  next_minor: Prims.unit -> FStar_Syntax_Syntax.version;}
let vops: vops_t =
  let major = FStar_Util.mk_ref (Prims.parse_int "0") in
  let minor = FStar_Util.mk_ref (Prims.parse_int "0") in
  let next_major uu____42 =
    FStar_ST.write minor (Prims.parse_int "0");
    (let uu____46 = FStar_Util.incr major; FStar_ST.read major in
     {
       FStar_Syntax_Syntax.major = uu____46;
       FStar_Syntax_Syntax.minor = (Prims.parse_int "0")
     }) in
  let next_minor uu____56 =
    let uu____57 = FStar_ST.read major in
    let uu____60 = FStar_Util.incr minor; FStar_ST.read minor in
    {
      FStar_Syntax_Syntax.major = uu____57;
      FStar_Syntax_Syntax.minor = uu____60
    } in
  { next_major; next_minor }
type tgraph = FStar_Syntax_Syntax.term option FStar_Unionfind.puf
type ugraph = FStar_Syntax_Syntax.universe option FStar_Unionfind.puf
type uf =
  {
  term_graph: tgraph;
<<<<<<< HEAD
  univ_graph: ugraph;
  version: FStar_Syntax_Syntax.version;}
let empty: FStar_Syntax_Syntax.version -> uf =
  fun v1  ->
    let uu____98 = FStar_Unionfind.puf_empty () in
    let uu____100 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____98; univ_graph = uu____100; version = v1 }
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____105 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____106 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____105 uu____106
let state: uf FStar_ST.ref =
  let uu____109 = let uu____110 = vops.next_major () in empty uu____110 in
  FStar_Util.mk_ref uu____109
=======
  univ_graph: ugraph;}
let __proj__Mkuf__item__term_graph: uf -> tgraph =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;_}
        -> __fname__term_graph
let __proj__Mkuf__item__univ_graph: uf -> ugraph =
  fun projectee  ->
    match projectee with
    | { term_graph = __fname__term_graph; univ_graph = __fname__univ_graph;_}
        -> __fname__univ_graph
>>>>>>> origin/guido_tactics
type tx =
  | TX of uf
let uu___is_TX: tx -> Prims.bool = fun projectee  -> true
let __proj__TX__item___0: tx -> uf =
  fun projectee  -> match projectee with | TX _0 -> _0
<<<<<<< HEAD
let get: Prims.unit -> uf = fun uu____125  -> FStar_ST.read state
let set: uf -> Prims.unit = fun u  -> FStar_ST.write state u
let reset: Prims.unit -> Prims.unit =
  fun uu____135  ->
    let v1 = vops.next_major () in let uu____137 = empty v1 in set uu____137
let new_transaction: Prims.unit -> tx =
  fun uu____140  ->
    let tx = let uu____142 = get () in TX uu____142 in
    (let uu____144 =
       let uu___99_145 = get () in
       let uu____146 = vops.next_minor () in
       {
         term_graph = (uu___99_145.term_graph);
         univ_graph = (uu___99_145.univ_graph);
         version = uu____146
       } in
     set uu____144);
    tx
let commit: tx -> Prims.unit = fun tx  -> ()
let rollback: tx -> Prims.unit =
  fun uu____152  -> match uu____152 with | TX uf -> set uf
let update_in_tx r x = ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____173  -> let uu____174 = get () in uu____174.term_graph
let get_version: Prims.unit -> FStar_Syntax_Syntax.version =
  fun uu____177  -> let uu____178 = get () in uu____178.version
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let uu____182 =
      let uu___100_183 = get () in
      {
        term_graph = tg;
        univ_graph = (uu___100_183.univ_graph);
        version = (uu___100_183.version)
      } in
    set uu____182
let chk_v uu____192 =
  match uu____192 with
  | (u,v1) ->
      let expected = get_version () in
      if
        (v1.FStar_Syntax_Syntax.major = expected.FStar_Syntax_Syntax.major)
          &&
          (v1.FStar_Syntax_Syntax.minor <= expected.FStar_Syntax_Syntax.minor)
      then u
      else
        (let uu____199 =
           let uu____200 = version_to_string expected in
           let uu____201 = version_to_string v1 in
           FStar_Util.format2
             "Incompatible version for unification variable: current version is %s; got version %s"
             uu____200 uu____201 in
         failwith uu____199)
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____205 = get_term_graph () in
    let uu____208 = chk_v u in FStar_Unionfind.puf_id uu____205 uu____208
let fresh:
  Prims.unit ->
    (FStar_Syntax_Syntax.term option FStar_Unionfind.p_uvar*
      FStar_Syntax_Syntax.version)
  =
  fun uu____218  ->
    let uu____219 =
      let uu____222 = get_term_graph () in
      FStar_Unionfind.puf_fresh uu____222 None in
    let uu____226 = get_version () in (uu____219, uu____226)
let find: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term option =
  fun u  ->
    let uu____233 = get_term_graph () in
    let uu____236 = chk_v u in FStar_Unionfind.puf_find uu____233 uu____236
=======
type transactional_state = {
  current: uf;
  rest: (tx* uf) Prims.list;}
let __proj__Mktransactional_state__item__current: transactional_state -> uf =
  fun projectee  ->
    match projectee with
    | { current = __fname__current; rest = __fname__rest;_} ->
        __fname__current
let __proj__Mktransactional_state__item__rest:
  transactional_state -> (tx* uf) Prims.list =
  fun projectee  ->
    match projectee with
    | { current = __fname__current; rest = __fname__rest;_} -> __fname__rest
let state: transactional_state FStar_ST.ref =
  let init1 =
    let uu____76 = FStar_Unionfind.puf_empty () in
    let uu____78 = FStar_Unionfind.puf_empty () in
    { term_graph = uu____76; univ_graph = uu____78 } in
  let tx_st = { current = init1; rest = [] } in FStar_Util.mk_ref tx_st
let get: Prims.unit -> uf =
  fun uu____87  -> let uu____88 = FStar_ST.read state in uu____88.current
let set: uf -> Prims.unit =
  fun u  ->
    let uu____95 =
      let uu___101_96 = FStar_ST.read state in
      { current = u; rest = (uu___101_96.rest) } in
    FStar_ST.write state uu____95
let reset: Prims.unit -> Prims.unit =
  fun uu____104  ->
    let uu____105 =
      let uu___102_106 = FStar_ST.read state in
      let uu____109 =
        let uu___103_110 =
          let uu____111 = FStar_ST.read state in uu____111.current in
        let uu____114 = FStar_Unionfind.puf_empty () in
        let uu____116 = FStar_Unionfind.puf_empty () in
        { term_graph = uu____114; univ_graph = uu____116 } in
      { current = uu____109; rest = (uu___102_106.rest) } in
    FStar_ST.write state uu____105
let new_transaction: Prims.unit -> tx =
  let tx_ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____126  ->
    let tx =
      FStar_Util.incr tx_ctr;
      (let uu____132 = FStar_ST.read tx_ctr in TX uu____132) in
    (let uu____136 =
       let uu___104_137 = FStar_ST.read state in
       let uu____140 =
         let uu____144 = let uu____147 = get () in (tx, uu____147) in
         let uu____148 =
           let uu____152 = FStar_ST.read state in uu____152.rest in
         uu____144 :: uu____148 in
       { current = (uu___104_137.current); rest = uu____140 } in
     FStar_ST.write state uu____136);
    tx
let commit_or_rollback: Prims.bool -> tx -> Prims.unit =
  fun rb  ->
    fun tx  ->
      let rec aux uu___100_173 =
        match uu___100_173 with
        | [] -> failwith "Transaction identifier is invalid"
        | (tx',uf)::rest ->
            if tx = tx'
            then
              (if rb then set uf else ();
               (let uu____189 =
                  let uu___105_190 = FStar_ST.read state in
                  { current = (uu___105_190.current); rest } in
                FStar_ST.write state uu____189))
            else aux rest in
      let uu____196 = let uu____200 = FStar_ST.read state in uu____200.rest in
      aux uu____196
let rollback: tx -> Prims.unit = fun tx  -> commit_or_rollback true tx
let commit: tx -> Prims.unit = fun tx  -> commit_or_rollback false tx
let update_in_tx r x = ()
let get_term_graph: Prims.unit -> tgraph =
  fun uu____234  -> let uu____235 = get () in uu____235.term_graph
let set_term_graph: tgraph -> Prims.unit =
  fun tg  ->
    let next =
      let uu___106_241 = get () in
      { term_graph = tg; univ_graph = (uu___106_241.univ_graph) } in
    let uu____242 =
      let uu___107_243 = FStar_ST.read state in
      { current = next; rest = (uu___107_243.rest) } in
    FStar_ST.write state uu____242
let uvar_id: FStar_Syntax_Syntax.uvar -> Prims.int =
  fun u  ->
    let uu____252 = get_term_graph () in FStar_Unionfind.puf_id uu____252 u
let fresh:
  Prims.unit -> FStar_Syntax_Syntax.term option FStar_Unionfind.p_uvar =
  fun uu____259  ->
    let uu____260 = get_term_graph () in
    FStar_Unionfind.puf_fresh uu____260 None
let find: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term option =
  fun u  ->
    let uu____269 = get_term_graph () in FStar_Unionfind.puf_find uu____269 u
>>>>>>> origin/guido_tactics
let change:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun u  ->
    fun t  ->
<<<<<<< HEAD
      let uu____250 =
        let uu____251 = get_term_graph () in
        let uu____254 = chk_v u in
        FStar_Unionfind.puf_change uu____251 uu____254 (Some t) in
      set_term_graph uu____250
=======
      let uu____281 =
        let uu____282 = get_term_graph () in
        FStar_Unionfind.puf_change uu____282 u (Some t) in
      set_term_graph uu____281
>>>>>>> origin/guido_tactics
let equiv: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
<<<<<<< HEAD
      let uu____268 = get_term_graph () in
      let uu____271 = chk_v u in
      let uu____278 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____268 uu____271 uu____278
=======
      let uu____294 = get_term_graph () in
      FStar_Unionfind.puf_equivalent uu____294 u v1
>>>>>>> origin/guido_tactics
let union: FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
<<<<<<< HEAD
      let uu____292 =
        let uu____293 = get_term_graph () in
        let uu____296 = chk_v u in
        let uu____303 = chk_v v1 in
        FStar_Unionfind.puf_union uu____293 uu____296 uu____303 in
      set_term_graph uu____292
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____313  -> let uu____314 = get () in uu____314.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let uu____318 =
      let uu___101_319 = get () in
      {
        term_graph = (uu___101_319.term_graph);
        univ_graph = ug;
        version = (uu___101_319.version)
      } in
    set uu____318
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____323 = get_univ_graph () in
    let uu____326 = chk_v u in FStar_Unionfind.puf_id uu____323 uu____326
let univ_fresh:
  Prims.unit ->
    (FStar_Syntax_Syntax.universe option FStar_Unionfind.p_uvar*
      FStar_Syntax_Syntax.version)
  =
  fun uu____334  ->
    let uu____335 =
      let uu____338 = get_univ_graph () in
      FStar_Unionfind.puf_fresh uu____338 None in
    let uu____342 = get_version () in (uu____335, uu____342)
let univ_find:
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe option =
  fun u  ->
    let uu____349 = get_univ_graph () in
    let uu____352 = chk_v u in FStar_Unionfind.puf_find uu____349 uu____352
=======
      let uu____306 =
        let uu____307 = get_term_graph () in
        FStar_Unionfind.puf_union uu____307 u v1 in
      set_term_graph uu____306
let get_univ_graph: Prims.unit -> ugraph =
  fun uu____314  -> let uu____315 = get () in uu____315.univ_graph
let set_univ_graph: ugraph -> Prims.unit =
  fun ug  ->
    let next =
      let uu___108_321 = get () in
      { term_graph = (uu___108_321.term_graph); univ_graph = ug } in
    let uu____322 =
      let uu___109_323 = FStar_ST.read state in
      { current = next; rest = (uu___109_323.rest) } in
    FStar_ST.write state uu____322
let univ_uvar_id: FStar_Syntax_Syntax.universe_uvar -> Prims.int =
  fun u  ->
    let uu____332 = get_univ_graph () in FStar_Unionfind.puf_id uu____332 u
let univ_fresh:
  Prims.unit -> FStar_Syntax_Syntax.universe option FStar_Unionfind.p_uvar =
  fun uu____339  ->
    let uu____340 = get_univ_graph () in
    FStar_Unionfind.puf_fresh uu____340 None
let univ_find:
  FStar_Syntax_Syntax.universe_uvar -> FStar_Syntax_Syntax.universe option =
  fun u  ->
    let uu____349 = get_univ_graph () in FStar_Unionfind.puf_find uu____349 u
>>>>>>> origin/guido_tactics
let univ_change:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe -> Prims.unit
  =
  fun u  ->
    fun t  ->
<<<<<<< HEAD
      let uu____364 =
        let uu____365 = get_univ_graph () in
        let uu____368 = chk_v u in
        FStar_Unionfind.puf_change uu____365 uu____368 (Some t) in
      set_univ_graph uu____364
=======
      let uu____361 =
        let uu____362 = get_univ_graph () in
        FStar_Unionfind.puf_change uu____362 u (Some t) in
      set_univ_graph uu____361
>>>>>>> origin/guido_tactics
let univ_equiv:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.bool
  =
  fun u  ->
    fun v1  ->
<<<<<<< HEAD
      let uu____380 = get_univ_graph () in
      let uu____383 = chk_v u in
      let uu____388 = chk_v v1 in
      FStar_Unionfind.puf_equivalent uu____380 uu____383 uu____388
=======
      let uu____374 = get_univ_graph () in
      FStar_Unionfind.puf_equivalent uu____374 u v1
>>>>>>> origin/guido_tactics
let univ_union:
  FStar_Syntax_Syntax.universe_uvar ->
    FStar_Syntax_Syntax.universe_uvar -> Prims.unit
  =
  fun u  ->
    fun v1  ->
<<<<<<< HEAD
      let uu____400 =
        let uu____401 = get_univ_graph () in
        let uu____404 = chk_v u in
        let uu____409 = chk_v v1 in
        FStar_Unionfind.puf_union uu____401 uu____404 uu____409 in
      set_univ_graph uu____400
=======
      let uu____386 =
        let uu____387 = get_univ_graph () in
        FStar_Unionfind.puf_union uu____387 u v1 in
      set_univ_graph uu____386
>>>>>>> origin/guido_tactics
