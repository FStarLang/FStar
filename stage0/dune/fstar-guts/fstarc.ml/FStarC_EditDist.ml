open Prims
let edit_distance (s1 : Prims.string) (s2 : Prims.string) : Prims.int=
  let cache = FStarC_IMap.create (Prims.of_int (10)) in
  let lookup i j =
    let uu___ = FStarC_IMap.try_find cache i in
    match uu___ with
    | FStar_Pervasives_Native.Some m -> FStarC_IMap.try_find m j
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
  let set i j d =
    let m =
      let uu___ = FStarC_IMap.try_find cache i in
      match uu___ with
      | FStar_Pervasives_Native.Some m1 -> m1
      | FStar_Pervasives_Native.None ->
          FStarC_IMap.create (Prims.of_int (10)) in
    FStarC_IMap.add m j d; FStarC_IMap.add cache i m in
  let l1 = FStarC_String.length s1 in
  let l2 = FStarC_String.length s2 in
  let rec go i1 i2 =
    if i1 = l1
    then l2 - i2
    else
      if i2 = l2
      then l1 - i1
      else
        (let uu___2 = lookup i1 i2 in
         match uu___2 with
         | FStar_Pervasives_Native.Some d -> d
         | FStar_Pervasives_Native.None ->
             let d =
               let uu___3 =
                 let uu___4 = FStarC_String.get s1 i1 in
                 let uu___5 = FStarC_String.get s2 i2 in uu___4 = uu___5 in
               if uu___3
               then go (i1 + Prims.int_one) (i2 + Prims.int_one)
               else
                 (let d1 = go (i1 + Prims.int_one) i2 in
                  let d2 = go i1 (i2 + Prims.int_one) in
                  let d3 = go (i1 + Prims.int_one) (i2 + Prims.int_one) in
                  (Prims.min (Prims.min d1 d2) d3) + Prims.int_one) in
             (set i1 i2 d; d)) in
  go Prims.int_zero Prims.int_zero
