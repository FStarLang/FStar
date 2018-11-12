module Bug057

val well_typed : o:(option nat){Some? o} -> u:unit{Some?.v o = 42}

val ill_typed : o:(option nat) -> Lemma
      (requires (Some? o))
      (ensures (Some?.v o = 42))
