module Bug1345b

assume val reg_t : Type

assume val range : n:nat -> list (m:nat{m < n})

assume val n_regtype : reg_t -> nat

type regtyp (t:reg_t) = n:nat{n < n_regtype t}

let reglist (t:reg_t) : list (regtyp t) = range (n_regtype t)
