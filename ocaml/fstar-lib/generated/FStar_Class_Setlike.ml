open Prims
type ('e, 's) setlike =
  {
  empty: unit -> 's ;
  singleton: 'e -> 's ;
  is_empty: 's -> Prims.bool ;
  add: 'e -> 's -> 's ;
  remove: 'e -> 's -> 's ;
  mem: 'e -> 's -> Prims.bool ;
  equal: 's -> 's -> Prims.bool ;
  subset: 's -> 's -> Prims.bool ;
  union: 's -> 's -> 's ;
  inter: 's -> 's -> 's ;
  diff: 's -> 's -> 's ;
  for_all: ('e -> Prims.bool) -> 's -> Prims.bool ;
  for_any: ('e -> Prims.bool) -> 's -> Prims.bool ;
  elems: 's -> 'e Prims.list ;
  collect: ('e -> 's) -> 'e Prims.list -> 's ;
  from_list: 'e Prims.list -> 's ;
  addn: 'e Prims.list -> 's -> 's }
let __proj__Mksetlike__item__empty :
  'e . unit -> ('e, Obj.t) setlike -> unit -> Obj.t =
  fun s ->
    fun x21 ->
      match x21 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} ->
          aempty
let empty : 'e . unit -> ('e, Obj.t) setlike -> unit -> Obj.t =
  fun s -> fun x21 -> __proj__Mksetlike__item__empty () x21
let __proj__Mksetlike__item__singleton :
  'e . unit -> ('e, Obj.t) setlike -> 'e -> Obj.t =
  fun s ->
    fun x22 ->
      match x22 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} ->
          asingleton
let singleton : 'e . unit -> ('e, Obj.t) setlike -> 'e -> Obj.t =
  fun s -> fun x22 -> __proj__Mksetlike__item__singleton () x22
let __proj__Mksetlike__item__is_empty :
  'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Prims.bool =
  fun s ->
    fun x23 ->
      match x23 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} ->
          ais_empty
let is_empty : 'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Prims.bool =
  fun s -> fun x23 -> __proj__Mksetlike__item__is_empty () x23
let __proj__Mksetlike__item__add :
  'e . unit -> ('e, Obj.t) setlike -> 'e -> Obj.t -> Obj.t =
  fun s ->
    fun x24 ->
      match x24 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} -> aadd
let add : 'e . unit -> ('e, Obj.t) setlike -> 'e -> Obj.t -> Obj.t =
  fun s -> fun x24 -> __proj__Mksetlike__item__add () x24
let __proj__Mksetlike__item__remove :
  'e . unit -> ('e, Obj.t) setlike -> 'e -> Obj.t -> Obj.t =
  fun s ->
    fun x25 ->
      match x25 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} ->
          aremove
let remove : 'e . unit -> ('e, Obj.t) setlike -> 'e -> Obj.t -> Obj.t =
  fun s -> fun x25 -> __proj__Mksetlike__item__remove () x25
let __proj__Mksetlike__item__mem :
  'e . unit -> ('e, Obj.t) setlike -> 'e -> Obj.t -> Prims.bool =
  fun s ->
    fun x26 ->
      match x26 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} -> amem
let mem : 'e . unit -> ('e, Obj.t) setlike -> 'e -> Obj.t -> Prims.bool =
  fun s -> fun x26 -> __proj__Mksetlike__item__mem () x26
let __proj__Mksetlike__item__equal :
  'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Obj.t -> Prims.bool =
  fun s ->
    fun x27 ->
      match x27 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} ->
          aequal
let equal : 'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Obj.t -> Prims.bool
  = fun s -> fun x27 -> __proj__Mksetlike__item__equal () x27
let __proj__Mksetlike__item__subset :
  'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Obj.t -> Prims.bool =
  fun s ->
    fun x28 ->
      match x28 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} ->
          asubset
let subset : 'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Obj.t -> Prims.bool
  = fun s -> fun x28 -> __proj__Mksetlike__item__subset () x28
let __proj__Mksetlike__item__union :
  'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Obj.t -> Obj.t =
  fun s ->
    fun x29 ->
      match x29 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} ->
          aunion
let union : 'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Obj.t -> Obj.t =
  fun s -> fun x29 -> __proj__Mksetlike__item__union () x29
let __proj__Mksetlike__item__inter :
  'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Obj.t -> Obj.t =
  fun s ->
    fun x30 ->
      match x30 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} ->
          ainter
let inter : 'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Obj.t -> Obj.t =
  fun s -> fun x30 -> __proj__Mksetlike__item__inter () x30
let __proj__Mksetlike__item__diff :
  'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Obj.t -> Obj.t =
  fun s ->
    fun x31 ->
      match x31 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} ->
          adiff
let diff : 'e . unit -> ('e, Obj.t) setlike -> Obj.t -> Obj.t -> Obj.t =
  fun s -> fun x31 -> __proj__Mksetlike__item__diff () x31
let __proj__Mksetlike__item__for_all :
  'e .
    unit -> ('e, Obj.t) setlike -> ('e -> Prims.bool) -> Obj.t -> Prims.bool
  =
  fun s ->
    fun x32 ->
      match x32 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} ->
          afor_all
let for_all :
  'e .
    unit -> ('e, Obj.t) setlike -> ('e -> Prims.bool) -> Obj.t -> Prims.bool
  = fun s -> fun x32 -> __proj__Mksetlike__item__for_all () x32
let __proj__Mksetlike__item__for_any :
  'e .
    unit -> ('e, Obj.t) setlike -> ('e -> Prims.bool) -> Obj.t -> Prims.bool
  =
  fun s ->
    fun x33 ->
      match x33 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} ->
          afor_any
let for_any :
  'e .
    unit -> ('e, Obj.t) setlike -> ('e -> Prims.bool) -> Obj.t -> Prims.bool
  = fun s -> fun x33 -> __proj__Mksetlike__item__for_any () x33
let __proj__Mksetlike__item__elems :
  'e . unit -> ('e, Obj.t) setlike -> Obj.t -> 'e Prims.list =
  fun s ->
    fun x34 ->
      match x34 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} ->
          aelems
let elems : 'e . unit -> ('e, Obj.t) setlike -> Obj.t -> 'e Prims.list =
  fun s -> fun x34 -> __proj__Mksetlike__item__elems () x34
let __proj__Mksetlike__item__collect :
  'e . unit -> ('e, Obj.t) setlike -> ('e -> Obj.t) -> 'e Prims.list -> Obj.t
  =
  fun s ->
    fun x35 ->
      match x35 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} ->
          acollect
let collect :
  'e . unit -> ('e, Obj.t) setlike -> ('e -> Obj.t) -> 'e Prims.list -> Obj.t
  = fun s -> fun x35 -> __proj__Mksetlike__item__collect () x35
let __proj__Mksetlike__item__from_list :
  'e . unit -> ('e, Obj.t) setlike -> 'e Prims.list -> Obj.t =
  fun s ->
    fun x36 ->
      match x36 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} ->
          afrom_list
let from_list : 'e . unit -> ('e, Obj.t) setlike -> 'e Prims.list -> Obj.t =
  fun s -> fun x36 -> __proj__Mksetlike__item__from_list () x36
let __proj__Mksetlike__item__addn :
  'e . unit -> ('e, Obj.t) setlike -> 'e Prims.list -> Obj.t -> Obj.t =
  fun s ->
    fun x37 ->
      match x37 with
      | { empty = aempty; singleton = asingleton; is_empty = ais_empty;
          add = aadd; remove = aremove; mem = amem; equal = aequal;
          subset = asubset; union = aunion; inter = ainter; diff = adiff;
          for_all = afor_all; for_any = afor_any; elems = aelems;
          collect = acollect; from_list = afrom_list; addn = aaddn;_} ->
          aaddn
let addn :
  'e . unit -> ('e, Obj.t) setlike -> 'e Prims.list -> Obj.t -> Obj.t =
  fun s -> fun x37 -> __proj__Mksetlike__item__addn () x37
let symdiff : 'e 's . ('e, 's) setlike -> 's -> 's -> 's =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun uu___ ->
           fun s1 ->
             fun s2 ->
               Obj.magic
                 (diff () (Obj.magic uu___) (Obj.magic s1) (Obj.magic s2)))
          uu___2 uu___1 uu___