module Steel.PCM

let commutative #a (op:a -> a -> a) = forall x y. op x y == op y x
let associative #a (op:a -> a -> a) = forall x y z. (op x (op y z) == op (op x y) z)
let is_unit #a (op:a -> a -> a) (u:a) = forall x. op x u == x
let is_undef #a (op:a -> a -> a) (z:a) = forall x. op x z == z
let undef_inv #a (op:a -> a -> a) (z:a) = forall x y. op x y =!= z ==> x =!= z /\ y =!= z

let lem_commutative #a (op:a -> a -> a) = (x:a) -> (y:a) -> Lemma (op x y == op y x)
let lem_associative #a (op: a -> a -> a) = x:a -> y:a -> z:a -> Lemma (op x (op y z) == op (op x y) z)
let lem_is_unit #a (op:a -> a -> a) (u:a) = x:a -> Lemma (op x u == x)
let lem_is_undef #a (op:a -> a -> a) (z:a) = x:a -> Lemma (op x z == z)
let lem_undef_inv #a (op:a -> a -> a) (z:a) = x:a -> y:a -> Lemma (op x y =!= z ==> x =!= z /\ y =!= z)


noeq
type pcm (a:Type) = {
  op: a -> a -> a;
  one:a;
  undef:a;
  laws: unit -> squash (commutative op /\
                       associative op /\
                       is_unit op one /\
                       is_undef op undef /\
                       undef_inv op undef);
  comm:lem_commutative op;
  assoc:lem_associative op;
  is_unit:lem_is_unit op one;
  is_undef:lem_is_undef op undef;
  undef_inv:lem_undef_inv op undef;
}

let defined #a (pcm:pcm a) (x:a) = x =!= pcm.undef

let combinable (#a:Type) (pcm:pcm a) (x y: a) =
  pcm.op x y =!= pcm.undef

let compatible #a (pcm:pcm a) (x y:a) =
  defined pcm x /\
  defined pcm y /\
  (exists (frame:a). pcm.op frame x == y)

let compatible_refl #a (pcm:pcm a) (x:a{defined pcm x})
  : Lemma (compatible pcm x x)
  = pcm.is_unit x;
    pcm.comm x pcm.one;
    assert (pcm.op pcm.one x == x)

let frame_preserving #a (pcm:pcm a) (x y: a) =
  forall frame. defined pcm (pcm.op x frame) ==>
           defined pcm (pcm.op y frame)
