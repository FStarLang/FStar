open Prims
let isNone: 'a . 'a FStar_Pervasives_Native.option -> Prims.bool =
  fun uu___10_12  ->
    match uu___10_12 with
    | FStar_Pervasives_Native.None  -> true
    | FStar_Pervasives_Native.Some uu____15 -> false
let isSome: 'a . 'a FStar_Pervasives_Native.option -> Prims.bool =
  fun uu___11_27  ->
    match uu___11_27 with
    | FStar_Pervasives_Native.Some uu____30 -> true
    | FStar_Pervasives_Native.None  -> false
let map:
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option -> 'b FStar_Pervasives_Native.option
  =
  fun f  ->
    fun uu___12_58  ->
      match uu___12_58 with
      | FStar_Pervasives_Native.Some x ->
          let uu____64 = f x in FStar_Pervasives_Native.Some uu____64
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let mapTot:
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option -> 'b FStar_Pervasives_Native.option
  =
  fun f  ->
    fun uu___13_91  ->
      match uu___13_91 with
      | FStar_Pervasives_Native.Some x -> FStar_Pervasives_Native.Some (f x)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let get: 'a . 'a FStar_Pervasives_Native.option -> 'a =
  fun uu___14_108  ->
    match uu___14_108 with
    | FStar_Pervasives_Native.Some x -> x
    | FStar_Pervasives_Native.None  -> failwith "empty option"