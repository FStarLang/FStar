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

new_effect ALL_h = ALL (heap : Type)

new_effect {
  ALL_h (heap: Type) : a: Type -> wp: all_wp_h heap a -> Effect
  with
    return_wp = all_return heap
  ; bind_wp = all_bind_wp heap
  ; if_then_else = all_if_then_else heap
  ; ite_wp = all_ite_wp heap
  ; stronger = all_stronger heap
  ; close_wp = all_close_wp heap
  ; assert_p = all_assert_p heap
  ; assume_p = all_assume_p heap
  ; null_wp = all_null_wp heap
  ; trivial = all_trivial heap
}

[@ dm4f_bind_range]
reifiable reflectable
new_effect {
  TAC : a: Type -> Effect
  with
    repr = __tac
  ; bind = __bind
  ; return = __ret
  ; __get = __get
}

