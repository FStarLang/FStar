open Prims
type real =
  | Real of Prims.string 
let uu___is_Real (projectee : real) : Prims.bool= true
let __proj__Real__item___0 (projectee : real) : Prims.string=
  match projectee with | Real _0 -> _0
let rec dropWhile :
  'uuuuu . ('uuuuu -> Prims.bool) -> 'uuuuu Prims.list -> 'uuuuu Prims.list =
  fun f xs ->
    match xs with
    | [] -> []
    | x::xs1 ->
        let uu___ = f x in if uu___ then dropWhile f xs1 else x :: xs1
let int_frac (r : real) :
  (Prims.string * Prims.string) FStar_Pervasives_Native.option=
  match FStarC_String.split [46] (__proj__Real__item___0 r) with
  | i::f::[] ->
      let i1 = FStarC_String.list_of_string i in
      let f1 = FStarC_String.list_of_string f in
      let i2 = dropWhile (fun c -> c = 48) i1 in
      let f2 =
        let uu___ = dropWhile (fun c -> c = 48) (FStarC_List.rev f1) in
        FStarC_List.rev uu___ in
      let uu___ =
        let uu___1 = FStarC_String.string_of_list i2 in
        let uu___2 = FStarC_String.string_of_list f2 in (uu___1, uu___2) in
      FStar_Pervasives_Native.Some uu___
  | uu___ -> FStar_Pervasives_Native.None
let max (x : Prims.int) (y : Prims.int) : Prims.int= if x > y then x else y
let zeropad_match (f1 : Prims.string) (f2 : Prims.string) :
  (Prims.string * Prims.string)=
  let len = max (FStarC_String.length f1) (FStarC_String.length f2) in
  let f11 =
    let uu___ = FStarC_String.make (len - (FStarC_String.length f1)) 48 in
    Prims.strcat f1 uu___ in
  let f21 =
    let uu___ = FStarC_String.make (len - (FStarC_String.length f2)) 48 in
    Prims.strcat f2 uu___ in
  (f11, f21)
let cmp (r1 : real) (r2 : real) :
  FStarC_Order.order FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = int_frac r1 in let uu___2 = int_frac r2 in (uu___1, uu___2) in
  match uu___ with
  | (FStar_Pervasives_Native.Some (i1, f1), FStar_Pervasives_Native.Some
     (i2, f2)) ->
      let uu___1 = zeropad_match f1 f2 in
      (match uu___1 with
       | (f11, f21) ->
           let i11 = FStarC_Util.int_of_string i1 in
           let i21 = FStarC_Util.int_of_string i2 in
           let f12 = FStarC_Util.int_of_string f11 in
           let f22 = FStarC_Util.int_of_string f21 in
           let uu___2 =
             FStarC_Class_Ord.cmp
               (FStarC_Class_Ord.ord_tuple2 FStarC_Class_Ord.ord_int
                  FStarC_Class_Ord.ord_int) (i11, f12) (i21, f22) in
           FStar_Pervasives_Native.Some uu___2)
  | uu___1 -> FStar_Pervasives_Native.None
