open Prims
let map (f : 'a -> 'b) (uu___ : 'a FStar_Pervasives_Native.option) :
  'b FStar_Pervasives_Native.option=
  match uu___ with
  | FStar_Pervasives_Native.Some x ->
      let uu___1 = f x in FStar_Pervasives_Native.Some uu___1
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let must (uu___ : 'a FStar_Pervasives_Native.option) : 'a=
  match uu___ with
  | FStar_Pervasives_Native.Some x -> x
  | FStar_Pervasives_Native.None ->
      failwith "FStarC.Option.must: called on None"
let dflt (d : 'a) (uu___ : 'a FStar_Pervasives_Native.option) : 'a=
  match uu___ with
  | FStar_Pervasives_Native.Some x -> x
  | FStar_Pervasives_Native.None -> d
let rec find :
  'a .
    ('a -> Prims.bool) -> 'a Prims.list -> 'a FStar_Pervasives_Native.option
  =
  fun f xs ->
    match xs with
    | [] -> FStar_Pervasives_Native.None
    | x::xs1 ->
        let uu___ = f x in
        if uu___ then FStar_Pervasives_Native.Some x else find f xs1
let bind (o : 'a FStar_Pervasives_Native.option)
  (f : 'a -> 'b FStar_Pervasives_Native.option) :
  'b FStar_Pervasives_Native.option=
  match o with
  | FStar_Pervasives_Native.Some x -> f x
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let catch (o : 'a FStar_Pervasives_Native.option)
  (f : unit -> 'a FStar_Pervasives_Native.option) :
  'a FStar_Pervasives_Native.option=
  match o with
  | FStar_Pervasives_Native.Some x -> FStar_Pervasives_Native.Some x
  | FStar_Pervasives_Native.None -> f ()
let iter (f : 'a -> unit) (uu___ : 'a FStar_Pervasives_Native.option) : 
  unit=
  match uu___ with
  | FStar_Pervasives_Native.Some x -> f x
  | FStar_Pervasives_Native.None -> ()
