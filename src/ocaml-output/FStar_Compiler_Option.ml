open Prims
let isNone : 'a . 'a FStar_Pervasives_Native.option -> Prims.bool =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> true
    | FStar_Pervasives_Native.Some uu___1 -> false
let isSome : 'a . 'a FStar_Pervasives_Native.option -> Prims.bool =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.Some uu___1 -> true
    | FStar_Pervasives_Native.None -> false
let map :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option -> 'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun uu___ ->
      match uu___ with
      | FStar_Pervasives_Native.Some x ->
          let uu___1 = f x in FStar_Pervasives_Native.Some uu___1
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let mapTot :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option -> 'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun uu___ ->
      match uu___ with
      | FStar_Pervasives_Native.Some x -> FStar_Pervasives_Native.Some (f x)
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let get : 'a . 'a FStar_Pervasives_Native.option -> 'a =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.Some x -> x
    | FStar_Pervasives_Native.None -> failwith "empty option"