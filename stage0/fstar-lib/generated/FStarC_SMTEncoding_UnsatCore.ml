open Prims
type unsat_core = Prims.string Prims.list
let (filter :
  unsat_core ->
    FStarC_SMTEncoding_Term.decl Prims.list ->
      FStarC_SMTEncoding_Term.decl Prims.list)
  =
  fun core ->
    fun decls ->
      let rec aux theory =
        let theory_rev = FStarC_Compiler_List.rev theory in
        let uu___ =
          FStarC_Compiler_List.fold_left
            (fun uu___1 ->
               fun d ->
                 match uu___1 with
                 | (keep, n_retained, n_pruned) ->
                     (match d with
                      | FStarC_SMTEncoding_Term.Assume a ->
                          if
                            FStarC_Compiler_List.contains
                              a.FStarC_SMTEncoding_Term.assumption_name core
                          then
                            ((d :: keep), (n_retained + Prims.int_one),
                              n_pruned)
                          else
                            if
                              FStarC_Compiler_Util.starts_with
                                a.FStarC_SMTEncoding_Term.assumption_name "@"
                            then ((d :: keep), n_retained, n_pruned)
                            else
                              (keep, n_retained, (n_pruned + Prims.int_one))
                      | FStarC_SMTEncoding_Term.Module (name, decls1) ->
                          let uu___2 = aux decls1 in
                          (match uu___2 with
                           | (keep', n, m) ->
                               (((FStarC_SMTEncoding_Term.Module
                                    (name, keep')) :: keep),
                                 (n_retained + n), (n_pruned + m)))
                      | uu___2 -> ((d :: keep), n_retained, n_pruned)))
            ([FStarC_SMTEncoding_Term.Caption
                (Prims.strcat "UNSAT CORE USED: "
                   (FStarC_Compiler_String.concat ", " core))],
              Prims.int_zero, Prims.int_zero) theory_rev in
        match uu___ with
        | (keep, n_retained, n_pruned) -> (keep, n_retained, n_pruned) in
      let uu___ = aux decls in
      match uu___ with | (keep, uu___1, uu___2) -> keep