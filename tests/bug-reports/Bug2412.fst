module Bug2412

open FStar.Set

// Set.as_set was not extracting correctly; it was undefined
// in FStar_Set
let list_to_set (l:list nat) : Tot (Set.set nat) = 
  Set.as_set l

