open Prims
type vops_t =
  {
  next_major: unit -> FStarC_Syntax_Syntax.version ;
  next_minor: unit -> FStarC_Syntax_Syntax.version }
let __proj__Mkvops_t__item__next_major (projectee : vops_t) :
  unit -> FStarC_Syntax_Syntax.version=
  match projectee with | { next_major; next_minor;_} -> next_major
let __proj__Mkvops_t__item__next_minor (projectee : vops_t) :
  unit -> FStarC_Syntax_Syntax.version=
  match projectee with | { next_major; next_minor;_} -> next_minor
let vops : vops_t=
  let major = FStarC_Effect.mk_ref Prims.int_zero in
  let minor = FStarC_Effect.mk_ref Prims.int_zero in
  let next_major uu___ =
    FStarC_Effect.op_Colon_Equals minor Prims.int_zero;
    (let uu___2 = FStarC_Util.incr major; FStarC_Effect.op_Bang major in
     {
       FStarC_Syntax_Syntax.major = uu___2;
       FStarC_Syntax_Syntax.minor = Prims.int_zero
     }) in
  let next_minor uu___ =
    let uu___1 = FStarC_Effect.op_Bang major in
    let uu___2 = FStarC_Util.incr minor; FStarC_Effect.op_Bang minor in
    {
      FStarC_Syntax_Syntax.major = uu___1;
      FStarC_Syntax_Syntax.minor = uu___2
    } in
  { next_major; next_minor }
type tgraph =
  (FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option *
    FStarC_Syntax_Syntax.uvar_decoration) FStarC_Unionfind.puf
type ugraph =
  FStarC_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStarC_Unionfind.puf
type uf =
  {
  term_graph: tgraph ;
  univ_graph: ugraph ;
  version: FStarC_Syntax_Syntax.version ;
  ro: Prims.bool }
let __proj__Mkuf__item__term_graph (projectee : uf) : tgraph=
  match projectee with
  | { term_graph; univ_graph; version; ro;_} -> term_graph
let __proj__Mkuf__item__univ_graph (projectee : uf) : ugraph=
  match projectee with
  | { term_graph; univ_graph; version; ro;_} -> univ_graph
let __proj__Mkuf__item__version (projectee : uf) :
  FStarC_Syntax_Syntax.version=
  match projectee with | { term_graph; univ_graph; version; ro;_} -> version
let __proj__Mkuf__item__ro (projectee : uf) : Prims.bool=
  match projectee with | { term_graph; univ_graph; version; ro;_} -> ro
let empty (v : FStarC_Syntax_Syntax.version) : uf=
  let uu___ = FStarC_Unionfind.puf_empty () in
  let uu___1 = FStarC_Unionfind.puf_empty () in
  { term_graph = uu___; univ_graph = uu___1; version = v; ro = false }
let version_to_string (v : FStarC_Syntax_Syntax.version) : Prims.string=
  let uu___ =
    FStarC_Class_Show.show FStarC_Class_Show.showable_int
      v.FStarC_Syntax_Syntax.major in
  let uu___1 =
    FStarC_Class_Show.show FStarC_Class_Show.showable_int
      v.FStarC_Syntax_Syntax.minor in
  FStarC_Format.fmt2 "%s.%s" uu___ uu___1
let state : uf FStarC_Effect.ref=
  let uu___ = let uu___1 = vops.next_major () in empty uu___1 in
  FStarC_Effect.mk_ref uu___
type tx =
  | TX of uf 
let uu___is_TX (projectee : tx) : Prims.bool= true
let __proj__TX__item___0 (projectee : tx) : uf=
  match projectee with | TX _0 -> _0
let get (uu___ : unit) : uf= FStarC_Effect.op_Bang state
let set_ro (uu___ : unit) : unit=
  let s = get () in
  FStarC_Effect.op_Colon_Equals state
    {
      term_graph = (s.term_graph);
      univ_graph = (s.univ_graph);
      version = (s.version);
      ro = true
    }
let set_rw (uu___ : unit) : unit=
  let s = get () in
  FStarC_Effect.op_Colon_Equals state
    {
      term_graph = (s.term_graph);
      univ_graph = (s.univ_graph);
      version = (s.version);
      ro = false
    }
let with_uf_enabled (f : unit -> 'a) : 'a=
  let s = get () in
  set_rw ();
  (let restore uu___1 = if s.ro then set_ro () else () in
   let r =
     let uu___1 = FStarC_Options.trace_error () in
     if uu___1
     then f ()
     else
       (try (fun uu___3 -> match () with | () -> f ()) ()
        with | uu___3 -> (restore (); FStarC_Effect.raise uu___3)) in
   restore (); r)
let fail_if_ro (uu___ : unit) : unit=
  let uu___1 = let uu___2 = get () in uu___2.ro in
  if uu___1
  then
    FStarC_Errors.raise_error0 FStarC_Errors_Codes.Fatal_BadUvar ()
      (Obj.magic FStarC_Errors_Msg.is_error_message_string)
      (Obj.magic "Internal error: UF graph was in read-only mode")
  else ()
let set (u : uf) : unit= fail_if_ro (); FStarC_Effect.op_Colon_Equals state u
let reset (uu___ : unit) : unit=
  fail_if_ro ();
  (let v = vops.next_major () in
   let uu___2 =
     let uu___3 = empty v in
     {
       term_graph = (uu___3.term_graph);
       univ_graph = (uu___3.univ_graph);
       version = (uu___3.version);
       ro = false
     } in
   set uu___2)
let new_transaction (uu___ : unit) : tx=
  let tx1 = let uu___1 = get () in TX uu___1 in
  (let uu___2 =
     let uu___3 = get () in
     let uu___4 = vops.next_minor () in
     {
       term_graph = (uu___3.term_graph);
       univ_graph = (uu___3.univ_graph);
       version = uu___4;
       ro = (uu___3.ro)
     } in
   set uu___2);
  tx1
let commit (tx1 : tx) : unit= ()
let rollback (uu___ : tx) : unit= match uu___ with | TX uf1 -> set uf1
let update_in_tx (r : 'a FStarC_Effect.ref) (x : 'a) : unit= ()
let get_term_graph (uu___ : unit) : tgraph=
  let uu___1 = get () in uu___1.term_graph
let get_version (uu___ : unit) : FStarC_Syntax_Syntax.version=
  let uu___1 = get () in uu___1.version
let set_term_graph (tg : tgraph) : unit=
  let uu___ =
    let uu___1 = get () in
    {
      term_graph = tg;
      univ_graph = (uu___1.univ_graph);
      version = (uu___1.version);
      ro = (uu___1.ro)
    } in
  set uu___
let chk_v_t (su : FStarC_Syntax_Syntax.uvar) :
  (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option * FStarC_Syntax_Syntax.uvar_decoration)
    FStarC_Unionfind.p_uvar=
  let uu___ = su in
  match uu___ with
  | (u, v, rng) ->
      let uvar_to_string u1 =
        let uu___1 =
          let uu___2 = FStarC_Unionfind.puf_unique_id u1 in
          FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___2 in
        Prims.strcat "?" uu___1 in
      let expected = get_version () in
      if
        (v.FStarC_Syntax_Syntax.major = expected.FStarC_Syntax_Syntax.major)
          &&
          (v.FStarC_Syntax_Syntax.minor <=
             expected.FStarC_Syntax_Syntax.minor)
      then u
      else
        (let uu___2 =
           let uu___3 =
             let uu___4 =
               FStarC_Errors_Msg.text
                 "Internal error: incompatible version for term unification variable" in
             let uu___5 =
               let uu___6 = uvar_to_string u in
               FStar_Pprint.doc_of_string uu___6 in
             FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
           let uu___4 =
             let uu___5 =
               let uu___6 = FStarC_Errors_Msg.text "Current version: " in
               let uu___7 =
                 let uu___8 = version_to_string expected in
                 FStar_Pprint.doc_of_string uu___8 in
               FStar_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
             let uu___6 =
               let uu___7 =
                 let uu___8 = FStarC_Errors_Msg.text "Got version: " in
                 let uu___9 =
                   let uu___10 = version_to_string v in
                   FStar_Pprint.doc_of_string uu___10 in
                 FStar_Pprint.op_Hat_Slash_Hat uu___8 uu___9 in
               [uu___7] in
             uu___5 :: uu___6 in
           uu___3 :: uu___4 in
         FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range rng
           FStarC_Errors_Codes.Fatal_BadUvar ()
           (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
           (Obj.magic uu___2))
let uvar_id (u : FStarC_Syntax_Syntax.uvar) : Prims.int=
  let uu___ = get_term_graph () in
  let uu___1 = chk_v_t u in FStarC_Unionfind.puf_id uu___ uu___1
let uvar_unique_id (u : FStarC_Syntax_Syntax.uvar) : Prims.int=
  let uu___ = chk_v_t u in FStarC_Unionfind.puf_unique_id uu___
let fresh (decoration : FStarC_Syntax_Syntax.uvar_decoration)
  (rng : FStarC_Range_Type.t) : FStarC_Syntax_Syntax.uvar=
  fail_if_ro ();
  (let uu___1 =
     let uu___2 = get_term_graph () in
     FStarC_Unionfind.puf_fresh uu___2
       (FStar_Pervasives_Native.None, decoration) in
   let uu___2 = get_version () in (uu___1, uu___2, rng))
let find_core (u : FStarC_Syntax_Syntax.uvar) :
  (FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option *
    FStarC_Syntax_Syntax.uvar_decoration)=
  let uu___ = get_term_graph () in
  let uu___1 = chk_v_t u in FStarC_Unionfind.puf_find uu___ uu___1
let find (u : FStarC_Syntax_Syntax.uvar) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let uu___ = find_core u in FStar_Pervasives_Native.fst uu___
let find_decoration (u : FStarC_Syntax_Syntax.uvar) :
  FStarC_Syntax_Syntax.uvar_decoration=
  let uu___ = find_core u in FStar_Pervasives_Native.snd uu___
let change (u : FStarC_Syntax_Syntax.uvar) (t : FStarC_Syntax_Syntax.term) :
  unit=
  let uu___ = find_core u in
  match uu___ with
  | (uu___1, dec) ->
      let uu___2 =
        let uu___3 = get_term_graph () in
        let uu___4 = chk_v_t u in
        FStarC_Unionfind.puf_change uu___3 uu___4
          ((FStar_Pervasives_Native.Some t), dec) in
      set_term_graph uu___2
let change_decoration (u : FStarC_Syntax_Syntax.uvar)
  (d : FStarC_Syntax_Syntax.uvar_decoration) : unit=
  let uu___ = find_core u in
  match uu___ with
  | (t, uu___1) ->
      let uu___2 =
        let uu___3 = get_term_graph () in
        let uu___4 = chk_v_t u in
        FStarC_Unionfind.puf_change uu___3 uu___4 (t, d) in
      set_term_graph uu___2
let equiv (u : FStarC_Syntax_Syntax.uvar) (v : FStarC_Syntax_Syntax.uvar) :
  Prims.bool=
  let uu___ = get_term_graph () in
  let uu___1 = chk_v_t u in
  let uu___2 = chk_v_t v in
  FStarC_Unionfind.puf_equivalent uu___ uu___1 uu___2
let union (u : FStarC_Syntax_Syntax.uvar) (v : FStarC_Syntax_Syntax.uvar) :
  unit=
  let uu___ =
    let uu___1 = get_term_graph () in
    let uu___2 = chk_v_t u in
    let uu___3 = chk_v_t v in FStarC_Unionfind.puf_union uu___1 uu___2 uu___3 in
  set_term_graph uu___
let get_univ_graph (uu___ : unit) : ugraph=
  let uu___1 = get () in uu___1.univ_graph
let chk_v_u
  (uu___ :
    ('uuuuu FStarC_Unionfind.p_uvar * FStarC_Syntax_Syntax.version *
      FStarC_Range_Type.t))
  : 'uuuuu FStarC_Unionfind.p_uvar=
  match uu___ with
  | (u, v, rng) ->
      let uvar_to_string u1 =
        let uu___1 =
          let uu___2 = FStarC_Unionfind.puf_unique_id u1 in
          FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___2 in
        Prims.strcat "?" uu___1 in
      let expected = get_version () in
      if
        (v.FStarC_Syntax_Syntax.major = expected.FStarC_Syntax_Syntax.major)
          &&
          (v.FStarC_Syntax_Syntax.minor <=
             expected.FStarC_Syntax_Syntax.minor)
      then u
      else
        (let uu___2 =
           let uu___3 =
             let uu___4 =
               FStarC_Errors_Msg.text
                 "Internal error: incompatible version for universe unification variable" in
             let uu___5 =
               let uu___6 = uvar_to_string u in
               FStar_Pprint.doc_of_string uu___6 in
             FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
           let uu___4 =
             let uu___5 =
               let uu___6 = FStarC_Errors_Msg.text "Current version: " in
               let uu___7 =
                 let uu___8 = version_to_string expected in
                 FStar_Pprint.doc_of_string uu___8 in
               FStar_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
             let uu___6 =
               let uu___7 =
                 let uu___8 = FStarC_Errors_Msg.text "Got version: " in
                 let uu___9 =
                   let uu___10 = version_to_string v in
                   FStar_Pprint.doc_of_string uu___10 in
                 FStar_Pprint.op_Hat_Slash_Hat uu___8 uu___9 in
               [uu___7] in
             uu___5 :: uu___6 in
           uu___3 :: uu___4 in
         FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range rng
           FStarC_Errors_Codes.Fatal_BadUvar ()
           (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
           (Obj.magic uu___2))
let set_univ_graph (ug : ugraph) : unit=
  let uu___ =
    let uu___1 = get () in
    {
      term_graph = (uu___1.term_graph);
      univ_graph = ug;
      version = (uu___1.version);
      ro = (uu___1.ro)
    } in
  set uu___
let univ_uvar_id (u : FStarC_Syntax_Syntax.universe_uvar) : Prims.int=
  let uu___ = get_univ_graph () in
  let uu___1 = chk_v_u u in FStarC_Unionfind.puf_id uu___ uu___1
let univ_fresh (rng : FStarC_Range_Type.t) :
  FStarC_Syntax_Syntax.universe_uvar=
  fail_if_ro ();
  (let uu___1 =
     let uu___2 = get_univ_graph () in
     FStarC_Unionfind.puf_fresh uu___2 FStar_Pervasives_Native.None in
   let uu___2 = get_version () in (uu___1, uu___2, rng))
let univ_find (u : FStarC_Syntax_Syntax.universe_uvar) :
  FStarC_Syntax_Syntax.universe FStar_Pervasives_Native.option=
  let uu___ = get_univ_graph () in
  let uu___1 = chk_v_u u in FStarC_Unionfind.puf_find uu___ uu___1
let univ_change (u : FStarC_Syntax_Syntax.universe_uvar)
  (t : FStarC_Syntax_Syntax.universe) : unit=
  let uu___ =
    let uu___1 = get_univ_graph () in
    let uu___2 = chk_v_u u in
    FStarC_Unionfind.puf_change uu___1 uu___2
      (FStar_Pervasives_Native.Some t) in
  set_univ_graph uu___
let univ_equiv (u : FStarC_Syntax_Syntax.universe_uvar)
  (v : FStarC_Syntax_Syntax.universe_uvar) : Prims.bool=
  let uu___ = get_univ_graph () in
  let uu___1 = chk_v_u u in
  let uu___2 = chk_v_u v in
  FStarC_Unionfind.puf_equivalent uu___ uu___1 uu___2
let univ_union (u : FStarC_Syntax_Syntax.universe_uvar)
  (v : FStarC_Syntax_Syntax.universe_uvar) : unit=
  let uu___ =
    let uu___1 = get_univ_graph () in
    let uu___2 = chk_v_u u in
    let uu___3 = chk_v_u v in FStarC_Unionfind.puf_union uu___1 uu___2 uu___3 in
  set_univ_graph uu___
