module Steel.RA

class ra0 (t:Type) = {
  valid : t -> prop;
  core : t -> option t;
  comp : t -> t -> t;
}

let is_ext0 (#t:Type) (ra:ra0 t) (a b : t) =
  exists c. b == ra.comp a c

class ra_props (#t:Type) (ra : ra0 t) = {
  assoc       : a:_ -> b:_ -> c:_ -> Lemma (ra.comp a (ra.comp b c) == ra.comp (ra.comp a b) c);
  comm        : a:_ -> b:_ -> Lemma (ra.comp a b == ra.comp b a);
  coreid      : a:_ -> Lemma (Some? (ra.core a) ==> ra.comp (Some?.v (ra.core a)) a == a);
  coreidem    : a:_ -> Lemma (Some? (ra.core a) ==> ra.core (Some?.v (ra.core a)) == ra.core a);
  coremono    : a:_ -> b:_ -> Lemma ((Some? (ra.core a) /\ is_ext0 ra a b)
                               ==> (Some? (ra.core b) /\ is_ext0 ra (Some?.v (ra.core a)) (Some?.v (ra.core b))));
  validop     : a:_ -> b:_ ->  Lemma (ra.valid (ra.comp a b) ==> ra.valid a);
}

class ra (t:Type) = {
  ra_b : ra0 t ;
  ra_p : ra_props ra_b;
}

instance ira_b : #t:Type ->   ra t -> ra0 t = fun #_ d -> d.ra_b
instance ira_p : #t:Type -> r:ra t -> ra_props r.ra_b = fun #_ d -> d.ra_p

let (@@) (#t:Type) [| ra t |] (a b : t) = comp a b

let is_ext (#t:Type) [| ra t |] (a b : t) =
  exists c. b == a @@ c

let (<<<) (#t:Type) [| ra t |] (a b : t)  = is_ext a b

let frame_preserving (#t:Type) (ra:ra t) (v0 v1 : t) : prop =
   forall frame. valid (v0 @@ frame) ==> valid (v1 @@ frame)

let composable (#t:Type) [| ra t |] (x y : t) : prop =
    valid (comp x y)
