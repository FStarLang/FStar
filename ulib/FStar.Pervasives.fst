module FStar.Pervasives

(* An SMT-pattern to control unfolding inductives;
   In a proof, you can say `allow_inversion (option a)`
   to allow the SMT solver. cf. allow_inversion below
 *)
let inversion (a:Type) = True

let allow_inversion (a:Type)
  : Pure unit (requires True) (ensures (fun x -> inversion a))
  = ()

//allowing inverting option without having to globally increase the fuel just for this
val invertOption : a:Type -> Lemma
  (requires True)
  (ensures (forall (x:option a). None? x \/ Some? x))
  [SMTPatT (option a)]
let invertOption a = allow_inversion (option a)

type either 'a 'b =
  | Inl : v:'a -> either 'a 'b
  | Inr : v:'b -> either 'a 'b

(* 'a * 'b * 'c *)
type tuple3 'a 'b 'c =
  | Mktuple3: _1:'a
           -> _2:'b
           -> _3:'c
          -> tuple3 'a 'b 'c

(* 'a * 'b * 'c * 'd *)
type tuple4 'a 'b 'c 'd =
  | Mktuple4: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> tuple4 'a 'b 'c 'd

(* 'a * 'b * 'c * 'd * 'e *)
type tuple5 'a 'b 'c 'd 'e =
  | Mktuple5: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> tuple5 'a 'b 'c 'd 'e

(* 'a * 'b * 'c * 'd * 'e * 'f *)
type tuple6 'a 'b 'c 'd 'e 'f =
  | Mktuple6: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> _6:'f
           -> tuple6 'a 'b 'c 'd 'e 'f

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g *)
type tuple7 'a 'b 'c 'd 'e 'f 'g =
  | Mktuple7: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> _6:'f
           -> _7:'g
           -> tuple7 'a 'b 'c 'd 'e 'f 'g

(* 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h *)
type tuple8 'a 'b 'c 'd 'e 'f 'g 'h =
  | Mktuple8: _1:'a
           -> _2:'b
           -> _3:'c
           -> _4:'d
           -> _5:'e
           -> _6:'f
           -> _7:'g
           -> _8:'h
           -> tuple8 'a 'b 'c 'd 'e 'f 'g 'h

(* Concrete syntax (x:a & y:b x & c x y) *)
unopteq type dtuple3 (a:Type)
             (b:(a -> GTot Type))
             (c:(x:a -> b x -> GTot Type)) =
   | Mkdtuple3:_1:a
             -> _2:b _1
             -> _3:c _1 _2
             -> dtuple3 a b c

(* Concrete syntax (x:a & y:b x & z:c x y & d x y z) *)
unopteq type dtuple4 (a:Type)
             (b:(x:a -> GTot Type))
             (c:(x:a -> b x -> GTot Type))
             (d:(x:a -> y:b x -> z:c x y -> GTot Type)) =
 | Mkdtuple4:_1:a
           -> _2:b _1
           -> _3:c _1 _2
           -> _4:d _1 _2 _3
           -> dtuple4 a b c d

(* Concrete syntax (w:a & x:b w & y:c w x & z:d w x y & e w x y z) *)
unopteq type dtuple5 (a:Type)
             (b:(w:a -> GTot Type))
             (c:(w:a -> b w -> GTot Type))
             (d:(w:a -> x:b w -> y:c w x -> GTot Type))
             (e:(w:a -> x:b w -> y:c w x -> z:d w x y -> GTot Type)) =
 | Mkdtuple5:_1:a
           -> _2:b _1
           -> _3:c _1 _2
           -> _4:d _1 _2 _3
           -> _5:e _1 _2 _3 _4
           -> dtuple5 a b c d e

(* Concrete syntax (v:a & w:b v & x:c v w & y:d v w x & z:e v w x y & f v w x y z) *)
unopteq type dtuple6 (a:Type)
             (b:(v:a -> GTot Type))
             (c:(v:a -> b v -> GTot Type))
             (d:(v:a -> w:b v -> x:c v w -> GTot Type))
             (e:(v:a -> w:b v -> x:c v w -> y:d v w x -> GTot Type))
             (f:(v:a -> w:b v -> x:c v w -> y:d v w x -> z:e v w x y -> GTot Type)) =
 | Mkdtuple6:_1:a
           -> _2:b _1
           -> _3:c _1 _2
           -> _4:d _1 _2 _3
           -> _5:e _1 _2 _3 _4
           -> _6:f _1 _2 _3 _4 _5
           -> dtuple6 a b c d e f

(* Concrete syntax (u:a & v:b u & w:c u v & x:d u v w & y:e u v w x & z:f u v w x y & g u v w x y z) *)
unopteq type dtuple7 (a:Type)
             (b:(u:a -> GTot Type))
             (c:(u:a -> b u -> GTot Type))
             (d:(u:a -> v:b u -> w:c u v -> GTot Type))
             (e:(u:a -> v:b u -> w:c u v -> x:d u v w -> GTot Type))
             (f:(u:a -> v:b u -> w:c u v -> x:d u v w -> y:e u v w x -> GTot Type))
             (g:(u:a -> v:b u -> w:c u v -> x:d u v w -> y:e u v w x -> z:f u v w x y -> GTot Type)) =
 | Mkdtuple7:_1:a
           -> _2:b _1
           -> _3:c _1 _2
           -> _4:d _1 _2 _3
           -> _5:e _1 _2 _3 _4
           -> _6:f _1 _2 _3 _4 _5
           -> _7:g _1 _2 _3 _4 _5 _6
           -> dtuple7 a b c d e f g

(* Concrete syntax (t:a & u:b t & v:c t u & w:d t u v & x:e t u v w & y:f t u v w x & z:g t u v w x y & h t u v w x y z) *)
unopteq type dtuple8 (a:Type)
             (b:(t:a -> GTot Type))
             (c:(t:a -> b t -> GTot Type))
             (d:(t:a -> u:b t -> v:c t u -> GTot Type))
             (e:(t:a -> u:b t -> v:c t u -> w:d t u v -> GTot Type))
             (f:(t:a -> u:b t -> v:c t u -> w:d t u v -> x:e t u v w -> GTot Type))
             (g:(t:a -> u:b t -> v:c t u -> w:d t u v -> x:e t u v w -> y:f t u v w x -> GTot Type))
             (h:(t:a -> u:b t -> v:c t u -> w:d t u v -> x:e t u v w -> y:f t u v w x -> z:g t u v w x y -> GTot Type)) =
 | Mkdtuple8:_1:a
           -> _2:b _1
           -> _3:c _1 _2
           -> _4:d _1 _2 _3
           -> _5:e _1 _2 _3 _4
           -> _6:f _1 _2 _3 _4 _5
           -> _7:g _1 _2 _3 _4 _5 _6
           -> _8:h _1 _2 _3 _4 _5 _6 _7
           -> dtuple8 a b c d e f g h

val ignore: #a:Type -> a -> Tot unit
let ignore #a x = ()
