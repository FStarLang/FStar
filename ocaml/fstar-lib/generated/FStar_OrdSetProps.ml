open Prims
let rec fold :
  'a 'b .
    'a FStar_OrdSet.cmp ->
      ('a -> 'b -> 'b) -> ('a, unit) FStar_OrdSet.ordset -> 'b -> 'b
  =
  fun f ->
    fun g ->
      fun s ->
        fun x ->
          if s = (FStar_OrdSet.empty f)
          then x
          else
            (let uu___1 = FStar_OrdSet.choose f s in
             match uu___1 with
             | FStar_Pervasives_Native.Some e ->
                 let a_rest = fold f g (FStar_OrdSet.remove f e s) x in
                 g e a_rest)
let insert :
  'a .
    'a FStar_OrdSet.cmp ->
      'a -> ('a, unit) FStar_OrdSet.ordset -> ('a, unit) FStar_OrdSet.ordset
  =
  fun f ->
    fun x -> fun s -> FStar_OrdSet.union f (FStar_OrdSet.singleton f x) s
let union' :
  'a .
    'a FStar_OrdSet.cmp ->
      ('a, unit) FStar_OrdSet.ordset ->
        ('a, unit) FStar_OrdSet.ordset -> ('a, unit) FStar_OrdSet.ordset
  =
  fun f -> fun s1 -> fun s2 -> fold f (fun e -> fun s -> insert f e s) s1 s2