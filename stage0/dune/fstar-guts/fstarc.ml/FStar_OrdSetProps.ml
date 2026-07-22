open Prims
let rec fold :
  'a 'b .
    'a FStar_OrdSet.cmp ->
      ('a -> 'b -> 'b) -> ('a, Obj.t) FStar_OrdSet.ordset -> 'b -> 'b
  =
  fun f g s x ->
    if s = (FStar_OrdSet.empty f)
    then x
    else
      (let uu___ = FStar_OrdSet.choose f s in
       match uu___ with
       | FStar_Pervasives_Native.Some e ->
           let a_rest = fold f g (FStar_OrdSet.remove f e s) x in g e a_rest)
let insert (f : 'a FStar_OrdSet.cmp) (x : 'a)
  (s : ('a, Obj.t) FStar_OrdSet.ordset) : ('a, Obj.t) FStar_OrdSet.ordset=
  FStar_OrdSet.union f (FStar_OrdSet.singleton f x) s
let union' (f : 'a FStar_OrdSet.cmp) (s1 : ('a, Obj.t) FStar_OrdSet.ordset)
  (s2 : ('a, Obj.t) FStar_OrdSet.ordset) : ('a, Obj.t) FStar_OrdSet.ordset=
  fold f (fun e s -> insert f e s) s1 s2
