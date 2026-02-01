open Prims
let anyref : Prims.bool FStarC_Effect.ref= FStarC_Effect.mk_ref false
let _debug_all : Prims.bool FStarC_Effect.ref= FStarC_Effect.mk_ref false
let toggle_list :
  Prims.bool FStarC_Effect.ref FStarC_PSMap.t FStarC_Effect.ref=
  let uu___ = FStarC_PSMap.empty () in FStarC_Effect.mk_ref uu___
let dbg_level : Prims.int FStarC_Effect.ref=
  FStarC_Effect.mk_ref Prims.int_zero
type saved_state =
  {
  toggles: (Prims.string * Prims.bool) Prims.list ;
  any: Prims.bool ;
  all: Prims.bool ;
  level: Prims.int }
let __proj__Mksaved_state__item__toggles (projectee : saved_state) :
  (Prims.string * Prims.bool) Prims.list=
  match projectee with | { toggles; any; all; level;_} -> toggles
let __proj__Mksaved_state__item__any (projectee : saved_state) : Prims.bool=
  match projectee with | { toggles; any; all; level;_} -> any
let __proj__Mksaved_state__item__all (projectee : saved_state) : Prims.bool=
  match projectee with | { toggles; any; all; level;_} -> all
let __proj__Mksaved_state__item__level (projectee : saved_state) : Prims.int=
  match projectee with | { toggles; any; all; level;_} -> level
let snapshot (uu___ : unit) : saved_state=
  let uu___1 =
    let uu___2 = FStarC_Effect.op_Bang toggle_list in
    FStarC_PSMap.fold uu___2
      (fun k r acc ->
         let uu___3 = let uu___4 = FStarC_Effect.op_Bang r in (k, uu___4) in
         uu___3 :: acc) [] in
  let uu___2 = FStarC_Effect.op_Bang anyref in
  let uu___3 = FStarC_Effect.op_Bang _debug_all in
  let uu___4 = FStarC_Effect.op_Bang dbg_level in
  { toggles = uu___1; any = uu___2; all = uu___3; level = uu___4 }
let register_toggle (k : Prims.string) : Prims.bool FStarC_Effect.ref=
  let r = FStarC_Effect.mk_ref false in
  (let uu___1 = FStarC_Effect.op_Bang _debug_all in
   if uu___1 then FStarC_Effect.op_Colon_Equals r true else ());
  (let uu___2 =
     let uu___3 = FStarC_Effect.op_Bang toggle_list in
     FStarC_PSMap.add uu___3 k r in
   FStarC_Effect.op_Colon_Equals toggle_list uu___2);
  r
let get_toggle (k : Prims.string) : Prims.bool FStarC_Effect.ref=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang toggle_list in
    FStarC_PSMap.try_find uu___1 k in
  match uu___ with
  | FStar_Pervasives_Native.Some r -> r
  | FStar_Pervasives_Native.None -> register_toggle k
let restore (snapshot1 : saved_state) : unit=
  (let uu___1 = FStarC_Effect.op_Bang toggle_list in
   FStarC_PSMap.iter uu___1
     (fun k r -> FStarC_Effect.op_Colon_Equals r false));
  FStarC_List.iter
    (fun uu___2 ->
       match uu___2 with
       | (k, b) -> let r = get_toggle k in FStarC_Effect.op_Colon_Equals r b)
    snapshot1.toggles;
  FStarC_Effect.op_Colon_Equals anyref snapshot1.any;
  FStarC_Effect.op_Colon_Equals _debug_all snapshot1.all;
  FStarC_Effect.op_Colon_Equals dbg_level snapshot1.level
let list_all_toggles (uu___ : unit) : Prims.string Prims.list=
  let uu___1 = FStarC_Effect.op_Bang toggle_list in FStarC_PSMap.keys uu___1
let any (uu___ : unit) : Prims.bool=
  (FStarC_Effect.op_Bang anyref) || (FStarC_Effect.op_Bang _debug_all)
let tag (s : Prims.string) : unit=
  let uu___ = any () in
  if uu___
  then
    FStarC_Format.print_string (Prims.strcat "DEBUG:" (Prims.strcat s "\n"))
  else ()
let enable (uu___ : unit) : unit= FStarC_Effect.op_Colon_Equals anyref true
let low (uu___ : unit) : Prims.bool=
  (let uu___1 = FStarC_Effect.op_Bang dbg_level in uu___1 >= Prims.int_one)
    || (FStarC_Effect.op_Bang _debug_all)
let medium (uu___ : unit) : Prims.bool=
  (let uu___1 = FStarC_Effect.op_Bang dbg_level in
   uu___1 >= (Prims.of_int (2))) || (FStarC_Effect.op_Bang _debug_all)
let high (uu___ : unit) : Prims.bool=
  (let uu___1 = FStarC_Effect.op_Bang dbg_level in
   uu___1 >= (Prims.of_int (3))) || (FStarC_Effect.op_Bang _debug_all)
let extreme (uu___ : unit) : Prims.bool=
  (let uu___1 = FStarC_Effect.op_Bang dbg_level in
   uu___1 >= (Prims.of_int (4))) || (FStarC_Effect.op_Bang _debug_all)
let set_level_low (uu___ : unit) : unit=
  FStarC_Effect.op_Colon_Equals dbg_level Prims.int_one
let set_level_medium (uu___ : unit) : unit=
  FStarC_Effect.op_Colon_Equals dbg_level (Prims.of_int (2))
let set_level_high (uu___ : unit) : unit=
  FStarC_Effect.op_Colon_Equals dbg_level (Prims.of_int (3))
let set_level_extreme (uu___ : unit) : unit=
  FStarC_Effect.op_Colon_Equals dbg_level (Prims.of_int (4))
let enable_toggles (keys : Prims.string Prims.list) : unit=
  if Prims.uu___is_Cons keys then enable () else ();
  FStarC_List.iter
    (fun k ->
       match k with
       | "Low" -> set_level_low ()
       | "Medium" -> set_level_medium ()
       | "High" -> set_level_high ()
       | "Extreme" -> set_level_extreme ()
       | uu___1 ->
           let uu___2 =
             ((FStarC_String.length k) > Prims.int_zero) &&
               (let uu___3 = FStarC_String.get k Prims.int_zero in
                uu___3 = 45) in
           if uu___2
           then
             let k1 =
               FStarC_String.substring k Prims.int_one
                 ((FStarC_String.length k) - Prims.int_one) in
             let t = get_toggle k1 in FStarC_Effect.op_Colon_Equals t false
           else
             (let t = get_toggle k in FStarC_Effect.op_Colon_Equals t true))
    keys
let disable_all (uu___ : unit) : unit=
  FStarC_Effect.op_Colon_Equals anyref false;
  FStarC_Effect.op_Colon_Equals dbg_level Prims.int_zero;
  (let uu___3 = FStarC_Effect.op_Bang toggle_list in
   FStarC_PSMap.iter uu___3
     (fun k r -> FStarC_Effect.op_Colon_Equals r false))
let set_debug_all (uu___ : unit) : unit=
  FStarC_Effect.op_Colon_Equals _debug_all true;
  FStarC_Effect.op_Colon_Equals dbg_level (Prims.of_int (4));
  (let uu___3 = FStarC_Effect.op_Bang toggle_list in
   FStarC_PSMap.iter uu___3 (fun k r -> FStarC_Effect.op_Colon_Equals r true))
