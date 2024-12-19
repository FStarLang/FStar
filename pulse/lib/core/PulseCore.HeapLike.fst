module PulseCore.HeapLike
noeq
type splittable (a:Type) = {
  disjoint : a -> a -> prop;
  join : x:a -> y:a {disjoint x y } -> a;
  laws : squash (
    (forall (x:a) (y:a). disjoint x y <==> disjoint y x) /\
    (forall (x:a) (y:a) (z:a). disjoint y z /\ disjoint x (join y z) ==>
      disjoint x y /\
      disjoint x z /\
      disjoint (join x y) z /\
      disjoint (join x z) y /\
      join x (join y z) == join (join x y) z)
  )  
}
noeq
type lens (a:Type) (b:Type) = {
  get : a -> GTot b;
  put : b -> a -> GTot a;
  sa: splittable a;
  sb: splittable b;
  lens_laws : squash (
      (forall (x:a). put (get x) x == x) /\
      (forall (x:a) (y:b). get (put y x) == y) /\
      (forall (x:a) (y:b) (z:b). put z (put y x) == put z x
    )
  );
  law0: (x:a) -> (y:a) -> Lemma (
      sa.disjoint x y ==>
      sb.disjoint (get x) (get y) /\
      get (sa.join x y) == sb.join (get x) (get y)
  );
  law1: (x:a) -> (y:a) -> l:b -> m:b -> Lemma (
        sa.disjoint x y /\
        sb.disjoint l m ==>
        sa.disjoint (put l x) (put m y) /\
        sa.join (put l x) (put m y) == put (sb.join l m) (sa.join x y)
      )
}
