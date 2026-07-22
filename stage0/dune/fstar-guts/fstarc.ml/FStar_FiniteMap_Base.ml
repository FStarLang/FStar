open Prims
type ('a, 'b, 's) setfun_t =
  ('a, 'b FStar_Pervasives_Native.option)
    FStar_FunctionalExtensionality.restricted_t
type ('a, 'b) map =
  ('a FStar_FiniteSet_Base.set, ('a, 'b, Obj.t) setfun_t) Prims.dtuple2
let domain (m : ('a, 'b) map) : 'a FStar_FiniteSet_Base.set=
  let uu___ = m in match uu___ with | Prims.Mkdtuple2 (keys, uu___1) -> keys
let elements (m : ('a, 'b) map) : ('a, 'b, Obj.t) setfun_t=
  let uu___ = m in match uu___ with | Prims.Mkdtuple2 (uu___1, f) -> f
let mem (key : 'a) (m : ('a, 'b) map) : Prims.bool=
  FStar_FiniteSet_Base.mem key (domain m)
let rec key_in_item_list : 'a 'b . 'a -> ('a * 'b) Prims.list -> Prims.bool =
  fun key items ->
    match items with
    | [] -> false
    | (k, v)::tl -> (key = k) || (key_in_item_list key tl)
let rec item_list_doesnt_repeat_keys :
  'a 'b . ('a * 'b) Prims.list -> Prims.bool =
  fun items ->
    match items with
    | [] -> true
    | (k, v)::tl ->
        (Prims.op_Negation (key_in_item_list k tl)) &&
          (item_list_doesnt_repeat_keys tl)
let lookup (key : 'a) (m : ('a, 'b) map) : 'b=
  FStar_Pervasives_Native.__proj__Some__item__v (elements m key)
let emptymap (uu___ : unit) : ('a, 'b) map=
  Prims.Mkdtuple2
    ((FStar_FiniteSet_Base.emptyset ()),
      (fun x -> FStar_Pervasives_Native.None))
let glue (keys : 'a FStar_FiniteSet_Base.set) (f : ('a, 'b, Obj.t) setfun_t)
  : ('a, 'b) map= Prims.Mkdtuple2 (keys, f)
let insert (k : 'a) (v : 'b) (m : ('a, 'b) map) : ('a, 'b) map=
  let keys' = FStar_FiniteSet_Base.insert k (domain m) in
  let f' x = if x = k then FStar_Pervasives_Native.Some v else elements m x in
  Prims.Mkdtuple2 (keys', f')
let merge (m1 : ('a, 'b) map) (m2 : ('a, 'b) map) : ('a, 'b) map=
  let keys' = FStar_FiniteSet_Base.union (domain m1) (domain m2) in
  let f' x =
    if FStar_FiniteSet_Base.mem x (domain m2)
    then elements m2 x
    else elements m1 x in
  Prims.Mkdtuple2 (keys', f')
let subtract (m : ('a, 'b) map) (s : 'a FStar_FiniteSet_Base.set) :
  ('a, 'b) map=
  let keys' = FStar_FiniteSet_Base.difference (domain m) s in
  let f' x =
    if FStar_FiniteSet_Base.mem x keys'
    then elements m x
    else FStar_Pervasives_Native.None in
  Prims.Mkdtuple2 (keys', f')
let remove (key : 'a) (m : ('a, 'b) map) : ('a, 'b) map=
  subtract m (FStar_FiniteSet_Base.singleton key)
let notin (key : 'a) (m : ('a, 'b) map) : Prims.bool=
  Prims.op_Negation (mem key m)
