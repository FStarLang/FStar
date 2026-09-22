open Prims
type counter =
  {
  c_time: Prims.int FStarC_Effect.ref ;
  c_calls: Prims.int FStarC_Effect.ref }
let __proj__Mkcounter__item__c_time (projectee : counter) :
  Prims.int FStarC_Effect.ref=
  match projectee with | { c_time; c_calls;_} -> c_time
let __proj__Mkcounter__item__c_calls (projectee : counter) :
  Prims.int FStarC_Effect.ref=
  match projectee with | { c_time; c_calls;_} -> c_calls
let counters : counter FStarC_SMap.t= FStarC_SMap.create (Prims.of_int 50)
let get (name : Prims.string) : counter=
  let uu___ = FStarC_SMap.try_find counters name in
  match uu___ with
  | FStar_Pervasives_Native.Some c -> c
  | FStar_Pervasives_Native.None ->
      let c =
        let uu___1 = FStarC_Effect.mk_ref Prims.int_zero in
        let uu___2 = FStarC_Effect.mk_ref Prims.int_zero in
        { c_time = uu___1; c_calls = uu___2 } in
      (FStarC_SMap.add counters name c; c)
let children : Prims.int FStarC_Effect.ref=
  FStarC_Effect.mk_ref Prims.int_zero
let enabled : Prims.bool FStar_Pervasives_Native.option FStarC_Effect.ref=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let is_enabled (uu___ : unit) : Prims.bool=
  let uu___1 = FStarC_Effect.op_Bang enabled in
  match uu___1 with
  | FStar_Pervasives_Native.Some b -> b
  | FStar_Pervasives_Native.None ->
      let b =
        FStarC_Options.profile_enabled FStar_Pervasives_Native.None
          "FStarC.Custard" in
      (FStarC_Effect.op_Colon_Equals enabled (FStar_Pervasives_Native.Some b);
       b)
let timed (name : Prims.string) (f : unit -> 'a) : 'a=
  let uu___ = let uu___1 = is_enabled () in Prims.not uu___1 in
  if uu___
  then f ()
  else
    (let c = get name in
     let saved = FStarC_Effect.op_Bang children in
     FStarC_Effect.op_Colon_Equals children Prims.int_zero;
     (let uu___2 = FStarC_Timing.record_ns f in
      match uu___2 with
      | (res, elapsed) ->
          let mine = FStarC_Effect.op_Bang children in
          (FStarC_Effect.op_Colon_Equals children (saved + elapsed);
           (let uu___5 =
              let uu___6 =
                let uu___7 = FStarC_Effect.op_Bang c.c_time in
                uu___7 + elapsed in
              uu___6 - mine in
            FStarC_Effect.op_Colon_Equals c.c_time uu___5);
           (let uu___6 =
              let uu___7 = FStarC_Effect.op_Bang c.c_calls in
              uu___7 + Prims.int_one in
            FStarC_Effect.op_Colon_Equals c.c_calls uu___6);
           res)))
let count (name : Prims.string) : unit=
  let c = get name in
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang c.c_calls in uu___1 + Prims.int_one in
  FStarC_Effect.op_Colon_Equals c.c_calls uu___
let report (uu___ : unit) : unit=
  let uu___1 = let uu___2 = is_enabled () in Prims.not uu___2 in
  if uu___1
  then ()
  else
    (let rows = FStarC_SMap.fold counters (fun k v acc -> (k, v) :: acc) [] in
     let rows1 =
       FStarC_Util.sort_with
         (fun uu___2 uu___3 ->
            match (uu___2, uu___3) with
            | ((uu___4, a), (uu___5, b)) ->
                let uu___6 = FStarC_Effect.op_Bang b.c_time in
                let uu___7 = FStarC_Effect.op_Bang a.c_time in
                uu___6 - uu___7) rows in
     FStarC_Format.print_string "Custard, exclusive time by counter:\n";
     FStarC_List.iter
       (fun uu___4 ->
          match uu___4 with
          | (k, c) ->
              let uu___5 =
                let uu___6 =
                  let uu___7 = FStarC_Effect.op_Bang c.c_time in
                  uu___7 / (Prims.of_int 1000000) in
                FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___6 in
              let uu___6 =
                let uu___7 = FStarC_Effect.op_Bang c.c_calls in
                FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___7 in
              FStarC_Format.print3 "  %s ms\t%s\t(%s calls)\n" uu___5 k
                uu___6) rows1;
     FStarC_SMap.clear counters)
