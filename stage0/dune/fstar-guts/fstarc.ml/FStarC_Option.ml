open Prims
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
let must : 'a . 'a FStar_Pervasives_Native.option -> 'a =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.Some x -> x
    | FStar_Pervasives_Native.None ->
        failwith "FStarC.Option.must: called on None"
let dflt : 'a . 'a -> 'a FStar_Pervasives_Native.option -> 'a =
  fun d ->
    fun uu___ ->
      match uu___ with
      | FStar_Pervasives_Native.Some x -> x
      | FStar_Pervasives_Native.None -> d
let rec find :
  'a .
    ('a -> Prims.bool) -> 'a Prims.list -> 'a FStar_Pervasives_Native.option
  =
  fun f ->
    fun xs ->
      match xs with
      | [] -> FStar_Pervasives_Native.None
      | x::xs1 ->
          let uu___ = f x in
          if uu___ then FStar_Pervasives_Native.Some x else find f xs1
let bind :
  'a 'b .
    'a FStar_Pervasives_Native.option ->
      ('a -> 'b FStar_Pervasives_Native.option) ->
        'b FStar_Pervasives_Native.option
  =
  fun o ->
    fun f ->
      match o with
      | FStar_Pervasives_Native.Some x -> f x
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let catch :
  'a .
    'a FStar_Pervasives_Native.option ->
      (unit -> 'a FStar_Pervasives_Native.option) ->
        'a FStar_Pervasives_Native.option
  =
  fun o ->
    fun f ->
      match o with
      | FStar_Pervasives_Native.Some x -> FStar_Pervasives_Native.Some x
      | FStar_Pervasives_Native.None -> f ()
let iter : 'a . ('a -> unit) -> 'a FStar_Pervasives_Native.option -> unit =
  fun f ->
    fun uu___ ->
      match uu___ with
      | FStar_Pervasives_Native.Some x -> f x
      | FStar_Pervasives_Native.None -> ()
