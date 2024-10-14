open Prims
let (hashable_lident : FStarC_Ident.lident FStarC_Class_Hashable.hashable) =
  {
    FStarC_Class_Hashable.hash =
      (fun l ->
         let uu___ = FStarC_Class_Show.show FStarC_Ident.showable_lident l in
         FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_string
           uu___)
  }
let (hashable_ident : FStarC_Ident.ident FStarC_Class_Hashable.hashable) =
  {
    FStarC_Class_Hashable.hash =
      (fun i ->
         let uu___ = FStarC_Class_Show.show FStarC_Ident.showable_ident i in
         FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_string
           uu___)
  }
let (hashable_binding :
  FStarC_Syntax_Syntax.binding FStarC_Class_Hashable.hashable) =
  {
    FStarC_Class_Hashable.hash =
      (fun uu___ ->
         match uu___ with
         | FStarC_Syntax_Syntax.Binding_var bv ->
             FStarC_Class_Hashable.hash FStarC_Syntax_Hash.hashable_term
               bv.FStarC_Syntax_Syntax.sort
         | FStarC_Syntax_Syntax.Binding_lid (l, (us, t)) ->
             let uu___1 =
               let uu___2 = FStarC_Class_Hashable.hash hashable_lident l in
               let uu___3 =
                 FStarC_Class_Hashable.hash
                   (FStarC_Class_Hashable.hashable_list hashable_ident) us in
               FStarC_Hash.mix uu___2 uu___3 in
             let uu___2 =
               FStarC_Class_Hashable.hash FStarC_Syntax_Hash.hashable_term t in
             FStarC_Hash.mix uu___1 uu___2
         | FStarC_Syntax_Syntax.Binding_univ u ->
             FStarC_Class_Hashable.hash hashable_ident u)
  }
let (hashable_bv : FStarC_Syntax_Syntax.bv FStarC_Class_Hashable.hashable) =
  {
    FStarC_Class_Hashable.hash =
      (fun b ->
         FStarC_Class_Hashable.hash FStarC_Syntax_Hash.hashable_term
           b.FStarC_Syntax_Syntax.sort)
  }
let (hashable_fv : FStarC_Syntax_Syntax.fv FStarC_Class_Hashable.hashable) =
  {
    FStarC_Class_Hashable.hash =
      (fun f ->
         FStarC_Class_Hashable.hash hashable_lident
           (f.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v)
  }
let (hashable_binder :
  FStarC_Syntax_Syntax.binder FStarC_Class_Hashable.hashable) =
  {
    FStarC_Class_Hashable.hash =
      (fun b ->
         FStarC_Class_Hashable.hash hashable_bv
           b.FStarC_Syntax_Syntax.binder_bv)
  }
let (hashable_letbinding :
  FStarC_Syntax_Syntax.letbinding FStarC_Class_Hashable.hashable) =
  {
    FStarC_Class_Hashable.hash =
      (fun lb ->
         let uu___ =
           let uu___1 =
             FStarC_Class_Hashable.hash
               (FStarC_Class_Hashable.hashable_either hashable_bv hashable_fv)
               lb.FStarC_Syntax_Syntax.lbname in
           let uu___2 =
             FStarC_Class_Hashable.hash FStarC_Syntax_Hash.hashable_term
               lb.FStarC_Syntax_Syntax.lbtyp in
           FStarC_Hash.mix uu___1 uu___2 in
         let uu___1 =
           FStarC_Class_Hashable.hash FStarC_Syntax_Hash.hashable_term
             lb.FStarC_Syntax_Syntax.lbdef in
         FStarC_Hash.mix uu___ uu___1)
  }
let (hashable_pragma :
  FStarC_Syntax_Syntax.pragma FStarC_Class_Hashable.hashable) =
  {
    FStarC_Class_Hashable.hash =
      (fun uu___ ->
         match uu___ with
         | FStarC_Syntax_Syntax.ShowOptions ->
             FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_int
               Prims.int_one
         | FStarC_Syntax_Syntax.SetOptions s ->
             let uu___1 =
               FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_int
                 (Prims.of_int (2)) in
             let uu___2 =
               FStarC_Class_Hashable.hash
                 FStarC_Class_Hashable.hashable_string s in
             FStarC_Hash.mix uu___1 uu___2
         | FStarC_Syntax_Syntax.ResetOptions s ->
             let uu___1 =
               FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_int
                 (Prims.of_int (3)) in
             let uu___2 =
               FStarC_Class_Hashable.hash
                 (FStarC_Class_Hashable.hashable_option
                    FStarC_Class_Hashable.hashable_string) s in
             FStarC_Hash.mix uu___1 uu___2
         | FStarC_Syntax_Syntax.PushOptions s ->
             let uu___1 =
               FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_int
                 (Prims.of_int (4)) in
             let uu___2 =
               FStarC_Class_Hashable.hash
                 (FStarC_Class_Hashable.hashable_option
                    FStarC_Class_Hashable.hashable_string) s in
             FStarC_Hash.mix uu___1 uu___2
         | FStarC_Syntax_Syntax.PopOptions ->
             FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_int
               (Prims.of_int (5))
         | FStarC_Syntax_Syntax.RestartSolver ->
             FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_int
               (Prims.of_int (6))
         | FStarC_Syntax_Syntax.PrintEffectsGraph ->
             FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_int
               (Prims.of_int (7)))
  }
let rec (hash_sigelt : FStarC_Syntax_Syntax.sigelt -> FStarC_Hash.hash_code)
  = fun se -> hash_sigelt' se.FStarC_Syntax_Syntax.sigel
and (hash_sigelt' : FStarC_Syntax_Syntax.sigelt' -> FStarC_Hash.hash_code) =
  fun se ->
    match se with
    | FStarC_Syntax_Syntax.Sig_inductive_typ
        { FStarC_Syntax_Syntax.lid = lid; FStarC_Syntax_Syntax.us = us;
          FStarC_Syntax_Syntax.params = params;
          FStarC_Syntax_Syntax.num_uniform_params = num_uniform_params;
          FStarC_Syntax_Syntax.t = t; FStarC_Syntax_Syntax.mutuals = mutuals;
          FStarC_Syntax_Syntax.ds = ds;
          FStarC_Syntax_Syntax.injective_type_params = injective_type_params;_}
        ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      let uu___7 =
                        FStarC_Class_Hashable.hash
                          FStarC_Class_Hashable.hashable_int Prims.int_zero in
                      let uu___8 =
                        FStarC_Class_Hashable.hash hashable_lident lid in
                      FStarC_Hash.mix uu___7 uu___8 in
                    let uu___7 =
                      FStarC_Class_Hashable.hash
                        (FStarC_Class_Hashable.hashable_list hashable_ident)
                        us in
                    FStarC_Hash.mix uu___6 uu___7 in
                  let uu___6 =
                    FStarC_Class_Hashable.hash
                      (FStarC_Class_Hashable.hashable_list hashable_binder)
                      params in
                  FStarC_Hash.mix uu___5 uu___6 in
                let uu___5 =
                  FStarC_Class_Hashable.hash
                    (FStarC_Class_Hashable.hashable_option
                       FStarC_Class_Hashable.hashable_int) num_uniform_params in
                FStarC_Hash.mix uu___4 uu___5 in
              let uu___4 =
                FStarC_Class_Hashable.hash FStarC_Syntax_Hash.hashable_term t in
              FStarC_Hash.mix uu___3 uu___4 in
            let uu___3 =
              FStarC_Class_Hashable.hash
                (FStarC_Class_Hashable.hashable_list hashable_lident) mutuals in
            FStarC_Hash.mix uu___2 uu___3 in
          let uu___2 =
            FStarC_Class_Hashable.hash
              (FStarC_Class_Hashable.hashable_list hashable_lident) ds in
          FStarC_Hash.mix uu___1 uu___2 in
        let uu___1 =
          FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_bool
            injective_type_params in
        FStarC_Hash.mix uu___ uu___1
    | FStarC_Syntax_Syntax.Sig_bundle
        { FStarC_Syntax_Syntax.ses = ses; FStarC_Syntax_Syntax.lids = lids;_}
        ->
        let uu___ =
          let uu___1 =
            FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_int
              Prims.int_one in
          let uu___2 =
            (FStarC_Class_Hashable.hashable_list
               { FStarC_Class_Hashable.hash = hash_sigelt }).FStarC_Class_Hashable.hash
              ses in
          FStarC_Hash.mix uu___1 uu___2 in
        let uu___1 =
          FStarC_Class_Hashable.hash
            (FStarC_Class_Hashable.hashable_list hashable_lident) lids in
        FStarC_Hash.mix uu___ uu___1
    | FStarC_Syntax_Syntax.Sig_datacon
        { FStarC_Syntax_Syntax.lid1 = lid; FStarC_Syntax_Syntax.us1 = us;
          FStarC_Syntax_Syntax.t1 = t; FStarC_Syntax_Syntax.ty_lid = ty_lid;
          FStarC_Syntax_Syntax.num_ty_params = num_ty_params;
          FStarC_Syntax_Syntax.mutuals1 = mutuals;
          FStarC_Syntax_Syntax.injective_type_params1 = injective_type_params;_}
        ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 =
                      FStarC_Class_Hashable.hash
                        FStarC_Class_Hashable.hashable_int (Prims.of_int (2)) in
                    let uu___7 =
                      FStarC_Class_Hashable.hash hashable_lident lid in
                    FStarC_Hash.mix uu___6 uu___7 in
                  let uu___6 =
                    FStarC_Class_Hashable.hash
                      (FStarC_Class_Hashable.hashable_list hashable_ident) us in
                  FStarC_Hash.mix uu___5 uu___6 in
                let uu___5 =
                  FStarC_Class_Hashable.hash FStarC_Syntax_Hash.hashable_term
                    t in
                FStarC_Hash.mix uu___4 uu___5 in
              let uu___4 = FStarC_Class_Hashable.hash hashable_lident ty_lid in
              FStarC_Hash.mix uu___3 uu___4 in
            let uu___3 =
              FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_int
                num_ty_params in
            FStarC_Hash.mix uu___2 uu___3 in
          let uu___2 =
            FStarC_Class_Hashable.hash
              (FStarC_Class_Hashable.hashable_list hashable_lident) mutuals in
          FStarC_Hash.mix uu___1 uu___2 in
        let uu___1 =
          FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_bool
            injective_type_params in
        FStarC_Hash.mix uu___ uu___1
    | FStarC_Syntax_Syntax.Sig_declare_typ
        { FStarC_Syntax_Syntax.lid2 = lid; FStarC_Syntax_Syntax.us2 = us;
          FStarC_Syntax_Syntax.t2 = t;_}
        ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_int
                (Prims.of_int (3)) in
            let uu___3 = FStarC_Class_Hashable.hash hashable_lident lid in
            FStarC_Hash.mix uu___2 uu___3 in
          let uu___2 =
            FStarC_Class_Hashable.hash
              (FStarC_Class_Hashable.hashable_list hashable_ident) us in
          FStarC_Hash.mix uu___1 uu___2 in
        let uu___1 =
          FStarC_Class_Hashable.hash FStarC_Syntax_Hash.hashable_term t in
        FStarC_Hash.mix uu___ uu___1
    | FStarC_Syntax_Syntax.Sig_let
        { FStarC_Syntax_Syntax.lbs1 = lbs;
          FStarC_Syntax_Syntax.lids1 = lids;_}
        ->
        let uu___ =
          let uu___1 =
            FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_int
              (Prims.of_int (4)) in
          let uu___2 =
            FStarC_Class_Hashable.hash
              (FStarC_Class_Hashable.hashable_tuple2
                 FStarC_Class_Hashable.hashable_bool
                 (FStarC_Class_Hashable.hashable_list hashable_letbinding))
              lbs in
          FStarC_Hash.mix uu___1 uu___2 in
        let uu___1 =
          FStarC_Class_Hashable.hash
            (FStarC_Class_Hashable.hashable_list hashable_lident) lids in
        FStarC_Hash.mix uu___ uu___1
    | FStarC_Syntax_Syntax.Sig_assume
        { FStarC_Syntax_Syntax.lid3 = lid; FStarC_Syntax_Syntax.us3 = us;
          FStarC_Syntax_Syntax.phi1 = phi;_}
        ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_int
                (Prims.of_int (5)) in
            let uu___3 = FStarC_Class_Hashable.hash hashable_lident lid in
            FStarC_Hash.mix uu___2 uu___3 in
          let uu___2 =
            FStarC_Class_Hashable.hash
              (FStarC_Class_Hashable.hashable_list hashable_ident) us in
          FStarC_Hash.mix uu___1 uu___2 in
        let uu___1 =
          FStarC_Class_Hashable.hash FStarC_Syntax_Hash.hashable_term phi in
        FStarC_Hash.mix uu___ uu___1
    | FStarC_Syntax_Syntax.Sig_pragma p ->
        let uu___ =
          FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_int
            (Prims.of_int (6)) in
        let uu___1 = FStarC_Class_Hashable.hash hashable_pragma p in
        FStarC_Hash.mix uu___ uu___1
    | uu___ ->
        FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_int
          Prims.int_zero
let (hashable_sigelt :
  FStarC_Syntax_Syntax.sigelt FStarC_Class_Hashable.hashable) =
  { FStarC_Class_Hashable.hash = hash_sigelt }
let (hashable_env :
  FStarC_TypeChecker_Env.env FStarC_Class_Hashable.hashable) =
  {
    FStarC_Class_Hashable.hash =
      (fun e ->
         let uu___ =
           let uu___1 =
             let uu___2 =
               FStarC_Class_Hashable.hash
                 (FStarC_Class_Hashable.hashable_list hashable_binding)
                 e.FStarC_TypeChecker_Env.gamma in
             let uu___3 =
               FStarC_Class_Hashable.hash
                 (FStarC_Class_Hashable.hashable_list
                    (FStarC_Class_Hashable.hashable_tuple2
                       (FStarC_Class_Hashable.hashable_list hashable_lident)
                       hashable_sigelt)) e.FStarC_TypeChecker_Env.gamma_sig in
             FStarC_Hash.mix uu___2 uu___3 in
           let uu___2 =
             FStarC_Class_Hashable.hash
               (FStarC_Class_Hashable.hashable_list
                  (FStarC_Class_Hashable.hashable_tuple2
                     (FStarC_Class_Hashable.hashable_list
                        FStarC_Class_Hashable.hashable_string)
                     FStarC_Class_Hashable.hashable_bool))
               e.FStarC_TypeChecker_Env.proof_ns in
           FStarC_Hash.mix uu___1 uu___2 in
         let uu___1 =
           FStarC_Class_Hashable.hash FStarC_Class_Hashable.hashable_bool
             e.FStarC_TypeChecker_Env.admit in
         FStarC_Hash.mix uu___ uu___1)
  }
let (query_cache_ref :
  FStarC_Hash.hash_code FStarC_Compiler_RBSet.t FStarC_Compiler_Effect.ref) =
  let uu___ =
    Obj.magic
      (FStarC_Class_Setlike.empty ()
         (Obj.magic
            (FStarC_Compiler_RBSet.setlike_rbset
               FStarC_Class_Hashable.ord_hash_code)) ()) in
  FStarC_Compiler_Util.mk_ref uu___
let (on : unit -> Prims.bool) =
  fun uu___ -> (FStarC_Options.query_cache ()) && (FStarC_Options.ide ())
let (query_cache_add :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> unit) =
  fun g ->
    fun q ->
      let uu___ = on () in
      if uu___
      then
        let h =
          FStarC_Class_Hashable.hash
            (FStarC_Class_Hashable.hashable_tuple2 hashable_env
               FStarC_Syntax_Hash.hashable_term) (g, q) in
        let uu___1 =
          let uu___2 = FStarC_Compiler_Effect.op_Bang query_cache_ref in
          Obj.magic
            (FStarC_Class_Setlike.add ()
               (Obj.magic
                  (FStarC_Compiler_RBSet.setlike_rbset
                     FStarC_Class_Hashable.ord_hash_code)) h
               (Obj.magic uu___2)) in
        FStarC_Compiler_Effect.op_Colon_Equals query_cache_ref uu___1
      else ()
let (try_find_query_cache :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun g ->
    fun q ->
      let uu___ = on () in
      if uu___
      then
        let h =
          FStarC_Class_Hashable.hash
            (FStarC_Class_Hashable.hashable_tuple2 hashable_env
               FStarC_Syntax_Hash.hashable_term) (g, q) in
        let r =
          let uu___1 = FStarC_Compiler_Effect.op_Bang query_cache_ref in
          FStarC_Class_Setlike.mem ()
            (Obj.magic
               (FStarC_Compiler_RBSet.setlike_rbset
                  FStarC_Class_Hashable.ord_hash_code)) h (Obj.magic uu___1) in
        r
      else false