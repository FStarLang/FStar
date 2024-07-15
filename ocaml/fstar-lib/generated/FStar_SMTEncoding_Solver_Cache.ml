open Prims
let (hashable_lident : FStar_Ident.lident FStar_Class_Hashable.hashable) =
  {
    FStar_Class_Hashable.hash =
      (fun l ->
         let uu___ = FStar_Class_Show.show FStar_Ident.showable_lident l in
         FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_string uu___)
  }
let (hashable_ident : FStar_Ident.ident FStar_Class_Hashable.hashable) =
  {
    FStar_Class_Hashable.hash =
      (fun i ->
         let uu___ = FStar_Class_Show.show FStar_Ident.showable_ident i in
         FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_string uu___)
  }
let (hashable_binding :
  FStar_Syntax_Syntax.binding FStar_Class_Hashable.hashable) =
  {
    FStar_Class_Hashable.hash =
      (fun uu___ ->
         match uu___ with
         | FStar_Syntax_Syntax.Binding_var bv ->
             FStar_Class_Hashable.hash FStar_Syntax_Hash.hashable_term
               bv.FStar_Syntax_Syntax.sort
         | FStar_Syntax_Syntax.Binding_lid (l, (us, t)) ->
             let uu___1 =
               let uu___2 = FStar_Class_Hashable.hash hashable_lident l in
               let uu___3 =
                 FStar_Class_Hashable.hash
                   (FStar_Class_Hashable.hashable_list hashable_ident) us in
               FStar_Hash.mix uu___2 uu___3 in
             let uu___2 =
               FStar_Class_Hashable.hash FStar_Syntax_Hash.hashable_term t in
             FStar_Hash.mix uu___1 uu___2
         | FStar_Syntax_Syntax.Binding_univ u ->
             FStar_Class_Hashable.hash hashable_ident u)
  }
let (hashable_bv : FStar_Syntax_Syntax.bv FStar_Class_Hashable.hashable) =
  {
    FStar_Class_Hashable.hash =
      (fun b ->
         FStar_Class_Hashable.hash FStar_Syntax_Hash.hashable_term
           b.FStar_Syntax_Syntax.sort)
  }
let (hashable_fv : FStar_Syntax_Syntax.fv FStar_Class_Hashable.hashable) =
  {
    FStar_Class_Hashable.hash =
      (fun f ->
         FStar_Class_Hashable.hash hashable_lident
           (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
  }
let (hashable_binder :
  FStar_Syntax_Syntax.binder FStar_Class_Hashable.hashable) =
  {
    FStar_Class_Hashable.hash =
      (fun b ->
         FStar_Class_Hashable.hash hashable_bv
           b.FStar_Syntax_Syntax.binder_bv)
  }
let (hashable_letbinding :
  FStar_Syntax_Syntax.letbinding FStar_Class_Hashable.hashable) =
  {
    FStar_Class_Hashable.hash =
      (fun lb ->
         let uu___ =
           let uu___1 =
             FStar_Class_Hashable.hash
               (FStar_Class_Hashable.hashable_either hashable_bv hashable_fv)
               lb.FStar_Syntax_Syntax.lbname in
           let uu___2 =
             FStar_Class_Hashable.hash FStar_Syntax_Hash.hashable_term
               lb.FStar_Syntax_Syntax.lbtyp in
           FStar_Hash.mix uu___1 uu___2 in
         let uu___1 =
           FStar_Class_Hashable.hash FStar_Syntax_Hash.hashable_term
             lb.FStar_Syntax_Syntax.lbdef in
         FStar_Hash.mix uu___ uu___1)
  }
let (hashable_pragma :
  FStar_Syntax_Syntax.pragma FStar_Class_Hashable.hashable) =
  {
    FStar_Class_Hashable.hash =
      (fun uu___ ->
         match uu___ with
         | FStar_Syntax_Syntax.SetOptions s ->
             let uu___1 =
               FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_int
                 Prims.int_one in
             let uu___2 =
               FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_string
                 s in
             FStar_Hash.mix uu___1 uu___2
         | FStar_Syntax_Syntax.ResetOptions s ->
             let uu___1 =
               FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_int
                 (Prims.of_int (2)) in
             let uu___2 =
               FStar_Class_Hashable.hash
                 (FStar_Class_Hashable.hashable_option
                    FStar_Class_Hashable.hashable_string) s in
             FStar_Hash.mix uu___1 uu___2
         | FStar_Syntax_Syntax.PushOptions s ->
             let uu___1 =
               FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_int
                 (Prims.of_int (3)) in
             let uu___2 =
               FStar_Class_Hashable.hash
                 (FStar_Class_Hashable.hashable_option
                    FStar_Class_Hashable.hashable_string) s in
             FStar_Hash.mix uu___1 uu___2
         | FStar_Syntax_Syntax.PopOptions ->
             FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_int
               (Prims.of_int (4))
         | FStar_Syntax_Syntax.RestartSolver ->
             FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_int
               (Prims.of_int (5))
         | FStar_Syntax_Syntax.PrintEffectsGraph ->
             FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_int
               (Prims.of_int (6)))
  }
let rec (hash_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Hash.hash_code) =
  fun se -> hash_sigelt' se.FStar_Syntax_Syntax.sigel
and (hash_sigelt' : FStar_Syntax_Syntax.sigelt' -> FStar_Hash.hash_code) =
  fun se ->
    match se with
    | FStar_Syntax_Syntax.Sig_inductive_typ
        { FStar_Syntax_Syntax.lid = lid; FStar_Syntax_Syntax.us = us;
          FStar_Syntax_Syntax.params = params;
          FStar_Syntax_Syntax.num_uniform_params = num_uniform_params;
          FStar_Syntax_Syntax.t = t; FStar_Syntax_Syntax.mutuals = mutuals;
          FStar_Syntax_Syntax.ds = ds;
          FStar_Syntax_Syntax.injective_type_params = injective_type_params;_}
        ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      let uu___7 =
                        FStar_Class_Hashable.hash
                          FStar_Class_Hashable.hashable_int Prims.int_zero in
                      let uu___8 =
                        FStar_Class_Hashable.hash hashable_lident lid in
                      FStar_Hash.mix uu___7 uu___8 in
                    let uu___7 =
                      FStar_Class_Hashable.hash
                        (FStar_Class_Hashable.hashable_list hashable_ident)
                        us in
                    FStar_Hash.mix uu___6 uu___7 in
                  let uu___6 =
                    FStar_Class_Hashable.hash
                      (FStar_Class_Hashable.hashable_list hashable_binder)
                      params in
                  FStar_Hash.mix uu___5 uu___6 in
                let uu___5 =
                  FStar_Class_Hashable.hash
                    (FStar_Class_Hashable.hashable_option
                       FStar_Class_Hashable.hashable_int) num_uniform_params in
                FStar_Hash.mix uu___4 uu___5 in
              let uu___4 =
                FStar_Class_Hashable.hash FStar_Syntax_Hash.hashable_term t in
              FStar_Hash.mix uu___3 uu___4 in
            let uu___3 =
              FStar_Class_Hashable.hash
                (FStar_Class_Hashable.hashable_list hashable_lident) mutuals in
            FStar_Hash.mix uu___2 uu___3 in
          let uu___2 =
            FStar_Class_Hashable.hash
              (FStar_Class_Hashable.hashable_list hashable_lident) ds in
          FStar_Hash.mix uu___1 uu___2 in
        let uu___1 =
          FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_bool
            injective_type_params in
        FStar_Hash.mix uu___ uu___1
    | FStar_Syntax_Syntax.Sig_bundle
        { FStar_Syntax_Syntax.ses = ses; FStar_Syntax_Syntax.lids = lids;_}
        ->
        let uu___ =
          let uu___1 =
            FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_int
              Prims.int_one in
          let uu___2 =
            (FStar_Class_Hashable.hashable_list
               { FStar_Class_Hashable.hash = hash_sigelt }).FStar_Class_Hashable.hash
              ses in
          FStar_Hash.mix uu___1 uu___2 in
        let uu___1 =
          FStar_Class_Hashable.hash
            (FStar_Class_Hashable.hashable_list hashable_lident) lids in
        FStar_Hash.mix uu___ uu___1
    | FStar_Syntax_Syntax.Sig_datacon
        { FStar_Syntax_Syntax.lid1 = lid; FStar_Syntax_Syntax.us1 = us;
          FStar_Syntax_Syntax.t1 = t; FStar_Syntax_Syntax.ty_lid = ty_lid;
          FStar_Syntax_Syntax.num_ty_params = num_ty_params;
          FStar_Syntax_Syntax.mutuals1 = mutuals;
          FStar_Syntax_Syntax.injective_type_params1 = injective_type_params;_}
        ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      FStar_Class_Hashable.hash
                        FStar_Class_Hashable.hashable_int (Prims.of_int (2)) in
                    let uu___7 =
                      FStar_Class_Hashable.hash hashable_lident lid in
                    FStar_Hash.mix uu___6 uu___7 in
                  let uu___6 =
                    FStar_Class_Hashable.hash
                      (FStar_Class_Hashable.hashable_list hashable_ident) us in
                  FStar_Hash.mix uu___5 uu___6 in
                let uu___5 =
                  FStar_Class_Hashable.hash FStar_Syntax_Hash.hashable_term t in
                FStar_Hash.mix uu___4 uu___5 in
              let uu___4 = FStar_Class_Hashable.hash hashable_lident ty_lid in
              FStar_Hash.mix uu___3 uu___4 in
            let uu___3 =
              FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_int
                num_ty_params in
            FStar_Hash.mix uu___2 uu___3 in
          let uu___2 =
            FStar_Class_Hashable.hash
              (FStar_Class_Hashable.hashable_list hashable_lident) mutuals in
          FStar_Hash.mix uu___1 uu___2 in
        let uu___1 =
          FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_bool
            injective_type_params in
        FStar_Hash.mix uu___ uu___1
    | FStar_Syntax_Syntax.Sig_declare_typ
        { FStar_Syntax_Syntax.lid2 = lid; FStar_Syntax_Syntax.us2 = us;
          FStar_Syntax_Syntax.t2 = t;_}
        ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_int
                (Prims.of_int (3)) in
            let uu___3 = FStar_Class_Hashable.hash hashable_lident lid in
            FStar_Hash.mix uu___2 uu___3 in
          let uu___2 =
            FStar_Class_Hashable.hash
              (FStar_Class_Hashable.hashable_list hashable_ident) us in
          FStar_Hash.mix uu___1 uu___2 in
        let uu___1 =
          FStar_Class_Hashable.hash FStar_Syntax_Hash.hashable_term t in
        FStar_Hash.mix uu___ uu___1
    | FStar_Syntax_Syntax.Sig_let
        { FStar_Syntax_Syntax.lbs1 = lbs; FStar_Syntax_Syntax.lids1 = lids;_}
        ->
        let uu___ =
          let uu___1 =
            FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_int
              (Prims.of_int (4)) in
          let uu___2 =
            FStar_Class_Hashable.hash
              (FStar_Class_Hashable.hashable_tuple2
                 FStar_Class_Hashable.hashable_bool
                 (FStar_Class_Hashable.hashable_list hashable_letbinding))
              lbs in
          FStar_Hash.mix uu___1 uu___2 in
        let uu___1 =
          FStar_Class_Hashable.hash
            (FStar_Class_Hashable.hashable_list hashable_lident) lids in
        FStar_Hash.mix uu___ uu___1
    | FStar_Syntax_Syntax.Sig_assume
        { FStar_Syntax_Syntax.lid3 = lid; FStar_Syntax_Syntax.us3 = us;
          FStar_Syntax_Syntax.phi1 = phi;_}
        ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_int
                (Prims.of_int (5)) in
            let uu___3 = FStar_Class_Hashable.hash hashable_lident lid in
            FStar_Hash.mix uu___2 uu___3 in
          let uu___2 =
            FStar_Class_Hashable.hash
              (FStar_Class_Hashable.hashable_list hashable_ident) us in
          FStar_Hash.mix uu___1 uu___2 in
        let uu___1 =
          FStar_Class_Hashable.hash FStar_Syntax_Hash.hashable_term phi in
        FStar_Hash.mix uu___ uu___1
    | FStar_Syntax_Syntax.Sig_pragma p ->
        let uu___ =
          FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_int
            (Prims.of_int (6)) in
        let uu___1 = FStar_Class_Hashable.hash hashable_pragma p in
        FStar_Hash.mix uu___ uu___1
    | uu___ ->
        FStar_Class_Hashable.hash FStar_Class_Hashable.hashable_int
          Prims.int_zero
let (hashable_sigelt :
  FStar_Syntax_Syntax.sigelt FStar_Class_Hashable.hashable) =
  { FStar_Class_Hashable.hash = hash_sigelt }
let (hashable_env : FStar_TypeChecker_Env.env FStar_Class_Hashable.hashable)
  =
  {
    FStar_Class_Hashable.hash =
      (fun e ->
         let uu___ =
           let uu___1 =
             let uu___2 =
               FStar_Class_Hashable.hash
                 (FStar_Class_Hashable.hashable_list hashable_binding)
                 e.FStar_TypeChecker_Env.gamma in
             let uu___3 =
               FStar_Class_Hashable.hash
                 (FStar_Class_Hashable.hashable_list
                    (FStar_Class_Hashable.hashable_tuple2
                       (FStar_Class_Hashable.hashable_list hashable_lident)
                       hashable_sigelt)) e.FStar_TypeChecker_Env.gamma_sig in
             FStar_Hash.mix uu___2 uu___3 in
           let uu___2 =
             FStar_Class_Hashable.hash
               (FStar_Class_Hashable.hashable_list
                  (FStar_Class_Hashable.hashable_tuple2
                     (FStar_Class_Hashable.hashable_list
                        FStar_Class_Hashable.hashable_string)
                     FStar_Class_Hashable.hashable_bool))
               e.FStar_TypeChecker_Env.proof_ns in
           FStar_Hash.mix uu___1 uu___2 in
         let uu___1 =
           FStar_Class_Hashable.hash
             (FStar_Class_Hashable.hashable_tuple2
                FStar_Class_Hashable.hashable_bool
                FStar_Class_Hashable.hashable_bool)
             ((e.FStar_TypeChecker_Env.admit), (e.FStar_TypeChecker_Env.lax)) in
         FStar_Hash.mix uu___ uu___1)
  }
let (query_cache_ref :
  FStar_Hash.hash_code FStar_Compiler_RBSet.t FStar_Compiler_Effect.ref) =
  let uu___ =
    Obj.magic
      (FStar_Class_Setlike.empty ()
         (Obj.magic
            (FStar_Compiler_RBSet.setlike_rbset
               FStar_Class_Hashable.ord_hash_code)) ()) in
  FStar_Compiler_Util.mk_ref uu___
let (on : unit -> Prims.bool) =
  fun uu___ -> (FStar_Options.query_cache ()) && (FStar_Options.ide ())
let (query_cache_add :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit) =
  fun g ->
    fun q ->
      let uu___ = on () in
      if uu___
      then
        let h =
          FStar_Class_Hashable.hash
            (FStar_Class_Hashable.hashable_tuple2 hashable_env
               FStar_Syntax_Hash.hashable_term) (g, q) in
        let uu___1 =
          let uu___2 = FStar_Compiler_Effect.op_Bang query_cache_ref in
          Obj.magic
            (FStar_Class_Setlike.add ()
               (Obj.magic
                  (FStar_Compiler_RBSet.setlike_rbset
                     FStar_Class_Hashable.ord_hash_code)) h
               (Obj.magic uu___2)) in
        FStar_Compiler_Effect.op_Colon_Equals query_cache_ref uu___1
      else ()
let (try_find_query_cache :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g ->
    fun q ->
      let uu___ = on () in
      if uu___
      then
        let h =
          FStar_Class_Hashable.hash
            (FStar_Class_Hashable.hashable_tuple2 hashable_env
               FStar_Syntax_Hash.hashable_term) (g, q) in
        let r =
          let uu___1 = FStar_Compiler_Effect.op_Bang query_cache_ref in
          FStar_Class_Setlike.mem ()
            (Obj.magic
               (FStar_Compiler_RBSet.setlike_rbset
                  FStar_Class_Hashable.ord_hash_code)) h (Obj.magic uu___1) in
        r
      else false