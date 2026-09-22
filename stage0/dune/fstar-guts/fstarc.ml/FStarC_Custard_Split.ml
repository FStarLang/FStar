open Prims
let module_of (n : FStarC_Custard_Syntax.name) : Prims.string=
  match n.FStarC_Custard_Syntax.ns with
  | [] -> "Custard"
  | ns -> FStarC_String.concat "." ns
let rank_key (m : Prims.string) : Prims.string=
  match FStarC_String.split [46] (FStarC_String.lowercase m) with
  | "fstar"::"normsteps"::rest ->
      FStarC_String.concat "." ("fstarc" :: "normsteps" :: rest)
  | "fstar"::"stubs"::rest -> FStarC_String.concat "." ("fstarc" :: rest)
  | uu___ -> FStarC_String.lowercase m
let source_ranks (deps : FStarC_Parser_Dep.deps) : Prims.int FStarC_SMap.t=
  let rank = FStarC_SMap.create (Prims.of_int 100) in
  let n = FStarC_Effect.mk_ref Prims.int_zero in
  (let uu___1 = FStarC_Parser_Dep.topological_order deps rank_key in
   FStarC_List.iter
     (fun m ->
        (let uu___3 =
           let uu___4 = FStarC_Effect.op_Bang n in uu___4 + Prims.int_one in
         FStarC_Effect.op_Colon_Equals n uu___3);
        (let uu___3 = FStarC_Effect.op_Bang n in
         FStarC_SMap.add rank m uu___3)) uu___1);
  rank
let sccs (nodes : Prims.string Prims.list)
  (succ : Prims.string -> Prims.string Prims.list) :
  Prims.string Prims.list Prims.list=
  let index = FStarC_SMap.create (Prims.of_int 100) in
  let low = FStarC_SMap.create (Prims.of_int 100) in
  let onstack = FStarC_SMap.create (Prims.of_int 100) in
  let stack = FStarC_Effect.mk_ref [] in
  let next = FStarC_Effect.mk_ref Prims.int_zero in
  let out = FStarC_Effect.mk_ref [] in
  let get m k =
    let uu___ = FStarC_SMap.try_find m k in
    match uu___ with
    | FStar_Pervasives_Native.Some v -> v
    | FStar_Pervasives_Native.None -> Prims.int_zero in
  let rec go v =
    (let uu___1 = FStarC_Effect.op_Bang next in
     FStarC_SMap.add index v uu___1);
    (let uu___2 = FStarC_Effect.op_Bang next in FStarC_SMap.add low v uu___2);
    (let uu___3 =
       let uu___4 = FStarC_Effect.op_Bang next in uu___4 + Prims.int_one in
     FStarC_Effect.op_Colon_Equals next uu___3);
    (let uu___4 = let uu___5 = FStarC_Effect.op_Bang stack in v :: uu___5 in
     FStarC_Effect.op_Colon_Equals stack uu___4);
    FStarC_SMap.add onstack v true;
    (let uu___6 = succ v in
     FStarC_List.iter
       (fun w ->
          let uu___7 =
            let uu___8 = FStarC_SMap.try_find index w in
            match uu___8 with
            | FStar_Pervasives_Native.None -> true
            | uu___9 -> false in
          if uu___7
          then
            (go w;
             (let uu___9 =
                let uu___10 = get low w in
                let uu___11 = get low v in uu___10 < uu___11 in
              if uu___9
              then let uu___10 = get low w in FStarC_SMap.add low v uu___10
              else ()))
          else
            (let uu___8 =
               let uu___9 = FStarC_SMap.try_find onstack w in
               (FStar_Pervasives_Native.Some true) = uu___9 in
             if uu___8
             then
               let uu___9 =
                 let uu___10 = get index w in
                 let uu___11 = get low v in uu___10 < uu___11 in
               (if uu___9
                then
                  let uu___10 = get index w in FStarC_SMap.add low v uu___10
                else ())
             else ())) uu___6);
    (let uu___6 =
       let uu___7 = get low v in let uu___8 = get index v in uu___7 = uu___8 in
     if uu___6
     then
       let rec pop acc =
         let uu___7 = FStarC_Effect.op_Bang stack in
         match uu___7 with
         | [] -> acc
         | w::rest ->
             (FStarC_Effect.op_Colon_Equals stack rest;
              FStarC_SMap.add onstack w false;
              if w = v then w :: acc else pop (w :: acc)) in
       let uu___7 =
         let uu___8 = pop [] in
         let uu___9 = FStarC_Effect.op_Bang out in uu___8 :: uu___9 in
       FStarC_Effect.op_Colon_Equals out uu___7
     else ()) in
  FStarC_List.iter
    (fun v ->
       let uu___1 =
         let uu___2 = FStarC_SMap.try_find index v in
         match uu___2 with
         | FStar_Pervasives_Native.None -> true
         | uu___3 -> false in
       if uu___1 then go v else ()) nodes;
  (let uu___1 = FStarC_Effect.op_Bang out in FStarC_List.rev uu___1)
let module_ranks (deps : FStarC_Parser_Dep.deps)
  (prog : FStarC_Custard_Syntax.program) : Prims.int FStarC_SMap.t=
  let src = source_ranks deps in
  let src_of m =
    let uu___ = let uu___1 = rank_key m in FStarC_SMap.try_find src uu___1 in
    match uu___ with
    | FStar_Pervasives_Native.Some r -> r
    | FStar_Pervasives_Native.None -> Prims.int_zero in
  let owner = FStarC_SMap.create (Prims.of_int 100) in
  let ctors = FStarC_Custard_Simplify.ctor_owners prog in
  FStarC_List.iter
    (fun d ->
       let uu___1 =
         FStarC_Custard_Syntax.string_of_name
           (FStarC_Custard_Syntax.name_of_decl d) in
       let uu___2 = module_of (FStarC_Custard_Syntax.name_of_decl d) in
       FStarC_SMap.add owner uu___1 uu___2) prog;
  (let owner_of n =
     let n1 =
       let uu___1 = FStarC_SMap.try_find ctors n in
       match uu___1 with
       | FStar_Pervasives_Native.Some o -> o
       | FStar_Pervasives_Native.None -> n in
     FStarC_SMap.try_find owner n1 in
   let succ = FStarC_SMap.create (Prims.of_int 100) in
   let seen = FStarC_SMap.create (Prims.of_int 100) in
   let node m =
     let uu___1 =
       let uu___2 = FStarC_SMap.try_find seen m in
       match uu___2 with
       | FStar_Pervasives_Native.None -> true
       | uu___3 -> false in
     if uu___1
     then (FStarC_SMap.add seen m true; FStarC_SMap.add succ m [])
     else () in
   FStarC_List.iter
     (fun d ->
        let m = module_of (FStarC_Custard_Syntax.name_of_decl d) in
        node m;
        (let uu___3 = FStarC_Custard_Simplify.decl_deps d in
         FStarC_List.iter
           (fun n ->
              let uu___4 = owner_of n in
              match uu___4 with
              | FStar_Pervasives_Native.Some m' ->
                  if m' <> m
                  then
                    (node m';
                     (let es =
                        let uu___6 = FStarC_SMap.try_find succ m in
                        match uu___6 with
                        | FStar_Pervasives_Native.Some es1 -> es1
                        | FStar_Pervasives_Native.None -> [] in
                      if Prims.not (FStarC_List.mem m' es)
                      then FStarC_SMap.add succ m (m' :: es)
                      else ()))
                  else ()
              | FStar_Pervasives_Native.None -> ()) uu___3)) prog;
   (let by_source a b =
      let uu___2 = src_of a in let uu___3 = src_of b in uu___2 - uu___3 in
    let nodes =
      let uu___2 = FStarC_SMap.keys succ in
      FStarC_Util.sort_with by_source uu___2 in
    let succ_of m =
      let uu___2 = FStarC_SMap.try_find succ m in
      match uu___2 with
      | FStar_Pervasives_Native.Some es -> FStarC_Util.sort_with by_source es
      | FStar_Pervasives_Native.None -> [] in
    let rank = FStarC_SMap.create (Prims.of_int 100) in
    let n = FStarC_Effect.mk_ref Prims.int_zero in
    (let uu___3 = sccs nodes succ_of in
     FStarC_List.iter
       (fun comp ->
          let uu___4 = FStarC_Util.sort_with by_source comp in
          FStarC_List.iter
            (fun m ->
               (let uu___6 =
                  let uu___7 = FStarC_Effect.op_Bang n in
                  uu___7 + Prims.int_one in
                FStarC_Effect.op_Colon_Equals n uu___6);
               (let uu___6 = FStarC_Effect.op_Bang n in
                FStarC_SMap.add rank m uu___6)) uu___4) uu___3);
    (let uu___4 =
       let uu___5 = FStarC_SMap.keys src in
       FStarC_Util.sort_with by_source uu___5 in
     FStarC_List.iter
       (fun m ->
          let uu___5 =
            let uu___6 = FStarC_SMap.try_find rank m in
            match uu___6 with
            | FStar_Pervasives_Native.None -> true
            | uu___7 -> false in
          if uu___5
          then
            ((let uu___7 =
                let uu___8 = FStarC_Effect.op_Bang n in
                uu___8 + Prims.int_one in
              FStarC_Effect.op_Colon_Equals n uu___7);
             (let uu___7 = FStarC_Effect.op_Bang n in
              FStarC_SMap.add rank m uu___7))
          else ()) uu___4);
    rank))
let group_of (d : FStarC_Custard_Syntax.decl) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_List.tryFind FStarC_Custard_Syntax.uu___is_Rec
      (FStarC_Custard_Syntax.decl_flags d) in
  match uu___ with
  | FStar_Pervasives_Native.Some (FStarC_Custard_Syntax.Rec ns) ->
      let uu___1 = FStarC_List.map FStarC_Custard_Syntax.string_of_name ns in
      FStar_Pervasives_Native.Some uu___1
  | uu___1 -> FStar_Pervasives_Native.None
let groups (prog : FStarC_Custard_Syntax.program) :
  FStarC_Custard_Syntax.decl Prims.list Prims.list=
  let rec go acc g ds =
    match ds with
    | [] -> if acc = [] then [] else [FStarC_List.rev acc]
    | d::rest ->
        let g' = group_of d in
        if
          ((acc <> []) &&
             (match g' with
              | FStar_Pervasives_Native.Some v -> true
              | uu___ -> false))
            && (g' = g)
        then go (d :: acc) g' rest
        else
          (let uu___ = go [d] g' rest in
           FStar_List_Tot_Base.append
             (if acc = [] then [] else [FStarC_List.rev acc]) uu___) in
  go [] FStar_Pervasives_Native.None prog
let emits (d : FStarC_Custard_Syntax.decl) : Prims.bool=
  let uu___ =
    let uu___1 = FStarC_Custard_Syntax.imported_unit d in
    match uu___1 with
    | FStar_Pervasives_Native.None -> true
    | uu___2 -> false in
  if uu___
  then
    match d with
    | FStarC_Custard_Syntax.DExternal uu___1 -> false
    | FStarC_Custard_Syntax.DType t ->
        let uu___1 =
          FStarC_Custard_Syntax.has_flag t.FStarC_Custard_Syntax.dt_flags
            FStarC_Custard_Syntax.Realized in
        Prims.not uu___1
    | uu___1 -> true
  else false
let file_of (m : Prims.string) : Prims.string=
  let uu___ =
    FStarC_Custard_Builtins.is_realized_module (FStarC_String.split [46] m) in
  if uu___ then Prims.strcat "Custard." m else m
let avoid (foreign : Prims.string Prims.list) (m : Prims.string) :
  Prims.string=
  let rec go f fuel =
    if (fuel = Prims.int_zero) || (Prims.not (FStarC_List.mem f foreign))
    then f
    else go (Prims.strcat "Custard." f) (fuel - Prims.int_one) in
  let uu___ = file_of m in go uu___ (Prims.of_int 10)
let run (deps : FStarC_Parser_Dep.deps) (foreign : Prims.string Prims.list)
  (prog : FStarC_Custard_Syntax.program) :
  (Prims.string * FStarC_Custard_Syntax.program) Prims.list=
  let gs = groups prog in
  let rank = module_ranks deps prog in
  let rank_of m =
    let uu___ = FStarC_SMap.try_find rank m in
    match uu___ with
    | FStar_Pervasives_Native.Some r -> r
    | FStar_Pervasives_Native.None ->
        let uu___1 =
          let uu___2 = rank_key m in FStarC_SMap.try_find rank uu___2 in
        (match uu___1 with
         | FStar_Pervasives_Native.Some r -> r
         | FStar_Pervasives_Native.None -> Prims.int_zero) in
  let own = FStarC_Custard_Simplify.ctor_owners prog in
  let resolve n =
    let uu___ = FStarC_SMap.try_find own n in
    match uu___ with
    | FStar_Pervasives_Native.Some o -> o
    | FStar_Pervasives_Native.None -> n in
  let home = FStarC_SMap.create (Prims.of_int 100) in
  let chunks = FStarC_SMap.create (Prims.of_int 100) in
  let emit m ds =
    let r =
      let uu___ = FStarC_SMap.try_find chunks m in
      match uu___ with
      | FStar_Pervasives_Native.Some r1 -> r1
      | FStar_Pervasives_Native.None ->
          let r1 = FStarC_Effect.mk_ref [] in
          (FStarC_SMap.add chunks m r1; r1) in
    let uu___ =
      let uu___1 = FStarC_Effect.op_Bang r in
      FStar_List_Tot_Base.append (FStarC_List.rev ds) uu___1 in
    FStarC_Effect.op_Colon_Equals r uu___ in
  FStarC_List.iter
    (fun g ->
       let cands =
         let uu___1 =
           FStarC_List.collect
             (fun d ->
                let uu___2 = emits d in
                if uu___2
                then
                  let uu___3 =
                    module_of (FStarC_Custard_Syntax.name_of_decl d) in
                  [uu___3]
                else []) g in
         let uu___2 =
           FStarC_List.collect
             (fun d ->
                let uu___3 = FStarC_Custard_Simplify.decl_deps d in
                FStarC_List.collect
                  (fun n ->
                     let uu___4 =
                       let uu___5 = resolve n in
                       FStarC_SMap.try_find home uu___5 in
                     match uu___4 with
                     | FStar_Pervasives_Native.Some m -> [m]
                     | FStar_Pervasives_Native.None -> []) uu___3) g in
         FStar_List_Tot_Base.append uu___1 uu___2 in
       let own1 =
         match cands with
         | m::uu___1 -> m
         | [] ->
             module_of
               (FStarC_Custard_Syntax.name_of_decl (FStarC_List.hd g)) in
       let top =
         FStarC_List.fold_left
           (fun acc m ->
              let uu___1 =
                let uu___2 = rank_of m in
                let uu___3 = rank_of acc in uu___2 > uu___3 in
              if uu___1 then m else acc) own1 cands in
       let best =
         let uu___1 =
           let uu___2 = rank_of own1 in
           let uu___3 = rank_of top in uu___2 >= uu___3 in
         if uu___1 then own1 else top in
       FStarC_List.iter
         (fun d ->
            let uu___2 = emits d in
            if uu___2
            then
              let uu___3 =
                FStarC_Custard_Syntax.string_of_name
                  (FStarC_Custard_Syntax.name_of_decl d) in
              FStarC_SMap.add home uu___3 best
            else ()) g;
       emit best g) gs;
  (let names = FStarC_SMap.keys chunks in
   let names1 =
     FStarC_Util.sort_with
       (fun a b ->
          let uu___1 = rank_of a in let uu___2 = rank_of b in uu___1 - uu___2)
       names in
   let files =
     FStarC_List.collect
       (fun m ->
          let ds =
            let uu___1 = FStarC_SMap.try_find chunks m in
            match uu___1 with
            | FStar_Pervasives_Native.Some r ->
                let uu___2 = FStarC_Effect.op_Bang r in
                FStarC_List.rev uu___2
            | FStar_Pervasives_Native.None -> [] in
          if ds = []
          then []
          else
            (let uu___1 = let uu___2 = avoid foreign m in (uu___2, ds) in
             [uu___1])) names1 in
   let have = FStarC_SMap.create (Prims.of_int 100) in
   FStarC_List.iter
     (fun uu___2 ->
        match uu___2 with | (m, uu___3) -> FStarC_SMap.add have m true) files;
   (let want_empties =
      let uu___2 = FStarC_Options.custard_backend () in
      FStarC_List.mem uu___2 ["KrmlC"; "KrmlRust"] in
    let empties =
      if Prims.not want_empties
      then []
      else
        (let uu___2 = FStarC_Parser_Dep.topological_order deps (fun m -> m) in
         FStarC_List.collect
           (fun m ->
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 = FStarC_SMap.try_find have m in
                    match uu___6 with
                    | FStar_Pervasives_Native.Some v -> true
                    | uu___7 -> false in
                  if uu___5 then true else FStarC_List.mem m foreign in
                if uu___4
                then true
                else
                  FStarC_Custard_Builtins.is_realized_module
                    (FStarC_String.split [46] m) in
              if uu___3 then [] else (FStarC_SMap.add have m true; [(m, [])]))
           uu___2) in
    FStar_List_Tot_Base.append files empties))
