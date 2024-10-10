module FStar.DTuple5

(** Dependent quadruples, with sugar [x:a & y:b x & z:c x y & d x y z] *)
unopteq
type dtuple5
  (a: Type) (b: (x: a -> GTot Type)) (c: (x: a -> b x -> GTot Type))
  (d: (x: a -> y: b x -> z: c x y -> GTot Type))
  (e: (x: a -> y: b x -> z: c x y -> w: d x y z -> GTot Type))
  = | Mkdtuple5 : _1: a -> _2: b _1 -> _3: c _1 _2 -> _4: d _1 _2 _3 -> _5: e _1 _2 _3 _4 -> dtuple5 a b c d e
