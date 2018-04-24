module Ex2

let intro_monoid (m: Type) (u: m) (mult: (m -> m -> m))
  : Pure (monoid m)
    (requires
      (right_unitality_lemma m u mult /\ left_unitality_lemma m u mult /\ associativity_lemma m mult
      ))
    (ensures (fun mm -> Monoid?.unit mm == u /\ Monoid?.mult mm == mult)) = Monoid u mult () () ()

type intro_monoid (m: Type) (u: m) (mult: (m -> m -> m))
  : Pure (monoid m)
    (requires
      (right_unitality_lemma m u mult /\ left_unitality_lemma m u mult /\ associativity_lemma m mult
      ))
    (ensures (fun mm -> Monoid?.unit mm == u /\ Monoid?.mult mm == mult))
  = Monoid u mult () () ()

type intro_monoid
  : Pure (monoid m)
    (requires
      (right_unitality_lemma m u mult /\ left_unitality_lemma m u mult /\ associativity_lemma m mult
      ))
    (ensures (fun mm -> Monoid?.unit mm == u /\ Monoid?.mult mm == mult))
  = Monoid u mult () () ()

type intro_monoid
  (m: Type) (u: m) (mult: (m -> m -> m)) (m: Type) (u: m) (mult: (m -> m -> m)) (m: Type) (u: m)
  (mult: (m -> m -> m))
  : Pure (monoid m)
    (requires
      (right_unitality_lemma m u mult /\ left_unitality_lemma m u mult /\ associativity_lemma m mult
      ))
    (ensures (fun mm -> Monoid?.unit mm == u /\ Monoid?.mult mm == mult))
  = Monoid u mult () () ()

type t : Type 

type t = bla

type t : Type = bla

