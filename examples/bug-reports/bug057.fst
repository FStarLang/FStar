module Bug57

val well_typed : o:(option nat){is_Some o} -> u:unit{Some.v o = 42}
      
val ill_typed : o:(option nat) -> Lemma
      (requires (is_Some o))
      (ensures (Some.v o = 42))
