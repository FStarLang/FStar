open Prims
type counter =
  {
  cid: Prims.string ;
  total_time: Prims.int FStarC_Effect.ref ;
  running: Prims.bool FStarC_Effect.ref ;
  undercount: Prims.bool FStarC_Effect.ref }
let __proj__Mkcounter__item__cid (projectee : counter) : Prims.string=
  match projectee with | { cid; total_time; running; undercount;_} -> cid
let __proj__Mkcounter__item__total_time (projectee : counter) :
  Prims.int FStarC_Effect.ref=
  match projectee with
  | { cid; total_time; running; undercount;_} -> total_time
let __proj__Mkcounter__item__running (projectee : counter) :
  Prims.bool FStarC_Effect.ref=
  match projectee with | { cid; total_time; running; undercount;_} -> running
let __proj__Mkcounter__item__undercount (projectee : counter) :
  Prims.bool FStarC_Effect.ref=
  match projectee with
  | { cid; total_time; running; undercount;_} -> undercount
let json_of_counter (c : counter) : FStarC_Json.json=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 = FStarC_Effect.op_Bang c.total_time in
          FStarC_Json.JsonInt uu___4 in
        ("total_time", uu___3) in
      let uu___3 =
        let uu___4 =
          let uu___5 =
            let uu___6 = FStarC_Effect.op_Bang c.running in
            FStarC_Json.JsonBool uu___6 in
          ("running", uu___5) in
        let uu___5 =
          let uu___6 =
            let uu___7 =
              let uu___8 = FStarC_Effect.op_Bang c.undercount in
              FStarC_Json.JsonBool uu___8 in
            ("undercount", uu___7) in
          [uu___6] in
        uu___4 :: uu___5 in
      uu___2 :: uu___3 in
    ("id", (FStarC_Json.JsonStr (c.cid))) :: uu___1 in
  FStarC_Json.JsonAssoc uu___
let new_counter (cid : Prims.string) : counter=
  let uu___ = FStarC_Effect.mk_ref Prims.int_zero in
  let uu___1 = FStarC_Effect.mk_ref false in
  let uu___2 = FStarC_Effect.mk_ref false in
  { cid; total_time = uu___; running = uu___1; undercount = uu___2 }
let all_counters : counter FStarC_SMap.t=
  FStarC_SMap.create (Prims.of_int (20))
let create_or_lookup_counter (cid : Prims.string) : counter=
  let uu___ = FStarC_SMap.try_find all_counters cid in
  match uu___ with
  | FStar_Pervasives_Native.Some c -> c
  | FStar_Pervasives_Native.None ->
      let c = new_counter cid in (FStarC_SMap.add all_counters cid c; c)
let profile (f : unit -> 'a)
  (module_name : Prims.string FStar_Pervasives_Native.option)
  (cid : Prims.string) : 'a=
  let uu___ = FStarC_Options.profile_enabled module_name cid in
  if uu___
  then
    let c = create_or_lookup_counter cid in
    let uu___1 = FStarC_Effect.op_Bang c.running in
    (if uu___1
     then f ()
     else
       (try
          (fun uu___3 ->
             match () with
             | () ->
                 (FStarC_Effect.op_Colon_Equals c.running true;
                  (let uu___5 = FStarC_Timing.record_ns f in
                   match uu___5 with
                   | (res, elapsed) ->
                       ((let uu___7 =
                           let uu___8 = FStarC_Effect.op_Bang c.total_time in
                           uu___8 + elapsed in
                         FStarC_Effect.op_Colon_Equals c.total_time uu___7);
                        FStarC_Effect.op_Colon_Equals c.running false;
                        res)))) ()
        with
        | uu___3 ->
            (FStarC_Effect.op_Colon_Equals c.running false;
             FStarC_Effect.op_Colon_Equals c.undercount true;
             FStarC_Effect.raise uu___3)))
  else f ()
let report_json (tag : Prims.string) (c : counter) : unit=
  let counter1 = json_of_counter c in
  let uu___ =
    FStarC_Json.string_of_json
      (FStarC_Json.JsonAssoc
         [("tag", (FStarC_Json.JsonStr tag)); ("counter", counter1)]) in
  FStarC_Format.print1_error "%s\n" uu___
let report_human (tag : Prims.string) (c : counter) : unit=
  let warn =
    let uu___ = FStarC_Effect.op_Bang c.running in
    if uu___
    then " (Warning, this counter is still running)"
    else
      (let uu___2 = FStarC_Effect.op_Bang c.undercount in
       if uu___2
       then
         " (Warning, some operations raised exceptions and we not accounted for)"
       else "") in
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Effect.op_Bang c.total_time in
      uu___2 / (Prims.parse_int "1000000") in
    FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___1 in
  FStarC_Format.print4 "%s, profiled %s:\t %s ms%s\n" tag c.cid uu___ warn
let report (tag : Prims.string) (c : counter) : unit=
  let uu___ = FStarC_Options.message_format () in
  match uu___ with
  | FStarC_Options.Human -> report_human tag c
  | FStarC_Options.Json -> report_json tag c
let report_and_clear (tag : Prims.string) : unit=
  let ctrs = FStarC_SMap.fold all_counters (fun uu___ v l -> v :: l) [] in
  FStarC_SMap.clear all_counters;
  (let ctrs1 =
     FStarC_Util.sort_with
       (fun c1 c2 ->
          let uu___1 = FStarC_Effect.op_Bang c2.total_time in
          let uu___2 = FStarC_Effect.op_Bang c1.total_time in uu___1 - uu___2)
       ctrs in
   FStarC_List.iter (report tag) ctrs1)
