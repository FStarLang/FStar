module NArrows

class n_arrows_t (t:Type) = { ff : int }

let n_arrows (t:Type) {| n : n_arrows_t t |} = n.ff

instance n_arrow_int : n_arrows_t int = {ff = 0}

instance n_arrow_arr (a b : Type)  {| _ : n_arrows_t b |} : n_arrows_t (a -> b) = {ff=1 + n_arrows b}

let xxx = n_arrows (int -> nat -> int)

let _ = assert (xxx == 2)
