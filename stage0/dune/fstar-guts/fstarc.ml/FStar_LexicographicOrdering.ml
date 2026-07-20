open Prims


let tuple_to_dep_tuple (x : ('a * 'b)) : ('a, 'b) Prims.dtuple2=
  Prims.Mkdtuple2
    ((FStar_Pervasives_Native.fst x), (FStar_Pervasives_Native.snd x))

