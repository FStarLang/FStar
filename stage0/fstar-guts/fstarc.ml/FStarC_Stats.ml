open Prims
let enabled : Prims.bool FStarC_Effect.ref= FStarC_Effect.alloc false
let ever_enabled : Prims.bool FStarC_Effect.ref= FStarC_Effect.alloc false
type stat =
  {
  ns_tree: Prims.int ;
  ns_exn: Prims.int ;
  ns_sub: Prims.int ;
  ncalls: Prims.int }
let __proj__Mkstat__item__ns_tree (projectee : stat) : Prims.int=
  match projectee with | { ns_tree; ns_exn; ns_sub; ncalls;_} -> ns_tree
let __proj__Mkstat__item__ns_exn (projectee : stat) : Prims.int=
  match projectee with | { ns_tree; ns_exn; ns_sub; ncalls;_} -> ns_exn
let __proj__Mkstat__item__ns_sub (projectee : stat) : Prims.int=
  match projectee with | { ns_tree; ns_exn; ns_sub; ncalls;_} -> ns_sub
let __proj__Mkstat__item__ncalls (projectee : stat) : Prims.int=
  match projectee with | { ns_tree; ns_exn; ns_sub; ncalls;_} -> ncalls
let uu___0 : stat FStarC_Class_Monoid.monoid=
  {
    FStarC_Class_Monoid.mzero =
      {
        ns_tree = Prims.int_zero;
        ns_exn = Prims.int_zero;
        ns_sub = Prims.int_zero;
        ncalls = Prims.int_zero
      };
    FStarC_Class_Monoid.mplus =
      (fun s1 s2 ->
         {
           ns_tree = (s1.ns_tree + s2.ns_tree);
           ns_exn = (s1.ns_exn + s2.ns_exn);
           ns_sub = (s1.ns_sub + s2.ns_sub);
           ncalls = (s1.ncalls + s2.ncalls)
         })
  }
let st : (Prims.bool FStarC_Effect.ref * stat) FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int (10))
let stack : Prims.string Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let r_running (k : Prims.string) : Prims.bool FStarC_Effect.ref=
  let uu___ = FStarC_SMap.try_find st k in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      let r = FStarC_Effect.alloc false in
      (FStarC_SMap.add st k (r, (FStarC_Class_Monoid.mzero uu___0)); r)
  | FStar_Pervasives_Native.Some (r, uu___1) -> r
let add (k : Prims.string) (s1 : stat) : unit=
  let uu___ =
    let uu___1 = FStarC_SMap.try_find st k in
    match uu___1 with
    | FStar_Pervasives_Native.None ->
        let uu___2 = FStarC_Effect.alloc false in
        (uu___2, (FStarC_Class_Monoid.mzero uu___0))
    | FStar_Pervasives_Native.Some rs -> rs in
  match uu___ with
  | (r, s0) ->
      let uu___1 =
        let uu___2 = FStarC_Class_Monoid.mplus uu___0 s0 s1 in (r, uu___2) in
      FStarC_SMap.add st k uu___1
let do_record (key : Prims.string) (f : unit -> 'a) : 'a=
  (let uu___1 = let uu___2 = FStarC_Effect.op_Bang stack in key :: uu___2 in
   FStarC_Effect.op_Colon_Equals stack uu___1);
  (let running = r_running key in
   let was_running = FStarC_Effect.op_Bang running in
   FStarC_Effect.op_Colon_Equals running true;
   (let t0 = FStarC_Timing.now_ns () in
    let resexn =
      try
        (fun uu___2 ->
           match () with
           | () -> let uu___3 = f () in FStar_Pervasives.Inr uu___3) ()
      with | uu___2 -> FStar_Pervasives.Inl uu___2 in
    FStarC_Effect.op_Colon_Equals running was_running;
    (let t1 = FStarC_Timing.now_ns () in
     let ns = FStarC_Timing.diff_ns t0 t1 in
     (let uu___4 =
        let uu___5 = FStarC_Effect.op_Bang stack in FStarC_List.tl uu___5 in
      FStarC_Effect.op_Colon_Equals stack uu___4);
     if Prims.op_Negation was_running
     then
       (add key
          {
            ns_tree = ns;
            ns_exn = ((FStarC_Class_Monoid.mzero uu___0).ns_exn);
            ns_sub = ((FStarC_Class_Monoid.mzero uu___0).ns_sub);
            ncalls = ((FStarC_Class_Monoid.mzero uu___0).ncalls)
          };
        (let uu___6 = FStarC_Effect.op_Bang stack in
         match uu___6 with
         | [] -> ()
         | k_par::uu___7 ->
             add k_par
               {
                 ns_tree = ((FStarC_Class_Monoid.mzero uu___0).ns_tree);
                 ns_exn = ((FStarC_Class_Monoid.mzero uu___0).ns_exn);
                 ns_sub = ns;
                 ncalls = ((FStarC_Class_Monoid.mzero uu___0).ncalls)
               }))
     else ();
     add key
       {
         ns_tree = ((FStarC_Class_Monoid.mzero uu___0).ns_tree);
         ns_exn = ((FStarC_Class_Monoid.mzero uu___0).ns_exn);
         ns_sub = ((FStarC_Class_Monoid.mzero uu___0).ns_sub);
         ncalls = Prims.int_one
       };
     (match resexn with
      | FStar_Pervasives.Inr r -> r
      | FStar_Pervasives.Inl e ->
          (add key
             {
               ns_tree = ((FStarC_Class_Monoid.mzero uu___0).ns_tree);
               ns_exn = ns;
               ns_sub = ((FStarC_Class_Monoid.mzero uu___0).ns_sub);
               ncalls = ((FStarC_Class_Monoid.mzero uu___0).ncalls)
             };
           FStarC_Effect.raise e)))))
let record (key : Prims.string) (f : unit -> 'a) : 'a=
  let uu___ = FStarC_Effect.op_Bang enabled in
  if uu___ then do_record key f else f ()
let lpad (len : Prims.int) (s : Prims.string) : Prims.string=
  let l = FStarC_String.length s in
  if l >= len
  then s
  else
    (let uu___1 = FStarC_String.make (len - l) 32 in Prims.strcat uu___1 s)
let max (x : Prims.int) (y : Prims.int) : Prims.int= if x > y then x else y
let print_all (uu___ : unit) : Prims.string=
  let keys = FStarC_SMap.keys st in
  let points =
    FStarC_List.map
      (fun k ->
         let uu___1 =
           let uu___2 =
             let uu___3 = FStarC_SMap.try_find st k in
             FStar_Pervasives_Native.__proj__Some__item__v uu___3 in
           FStar_Pervasives_Native.snd uu___2 in
         (k, uu___1)) keys in
  let points1 =
    FStarC_Class_Ord.sort_by
      (fun uu___1 uu___2 ->
         match (uu___1, uu___2) with
         | ((uu___3, s1), (uu___4, s2)) ->
             FStarC_Class_Ord.cmp FStarC_Class_Ord.ord_int
               (s2.ns_tree - s2.ns_sub) (s1.ns_tree - s1.ns_sub)) points in
  let longest_key =
    FStarC_List.fold_left
      (fun acc uu___1 ->
         match uu___1 with | (k, uu___2) -> max acc (FStarC_String.length k))
      (Prims.of_int (20)) points1 in
  let pr1 p =
    let uu___1 = p in
    match uu___1 with
    | (k, st1) ->
        let uu___2 = lpad longest_key k in
        let uu___3 =
          let uu___4 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_int st1.ncalls in
          lpad (Prims.of_int (8)) uu___4 in
        let uu___4 =
          let uu___5 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_int
              (st1.ns_tree / (Prims.parse_int "1000000")) in
          lpad (Prims.of_int (6)) uu___5 in
        let uu___5 =
          let uu___6 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_int
              ((st1.ns_tree - st1.ns_sub) / (Prims.parse_int "1000000")) in
          lpad (Prims.of_int (6)) uu___6 in
        let uu___6 =
          let uu___7 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_int
              (st1.ns_exn / (Prims.parse_int "1000000")) in
          lpad (Prims.of_int (6)) uu___7 in
        FStarC_Format.fmt5 "  %s  %s %s ms %s ms %s ms" uu___2 uu___3 uu___4
          uu___5 uu___6 in
  let uu___1 =
    let uu___2 = lpad longest_key "key" in
    let uu___3 = lpad (Prims.of_int (8)) "calls" in
    let uu___4 = lpad (Prims.of_int (9)) "tree" in
    let uu___5 = lpad (Prims.of_int (9)) "point" in
    let uu___6 = lpad (Prims.of_int (9)) "exn" in
    FStarC_Format.fmt5 "  %s  %s %s %s %s" uu___2 uu___3 uu___4 uu___5 uu___6 in
  let uu___2 =
    let uu___3 =
      let uu___4 = FStarC_List.map pr1 points1 in
      FStarC_String.concat "\n" uu___4 in
    Prims.strcat "\n" uu___3 in
  Prims.strcat uu___1 uu___2
