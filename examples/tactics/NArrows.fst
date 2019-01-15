module NArrows

type n_arrows_t (t:Type) = int

let n_arrows (t:Type) [| n : n_arrows_t t |] = n

instance n_arrow_int : n_arrows_t int = 0

instance n_arrow_arr (a b : Type)  [| _ : n_arrows_t b |] : n_arrows_t (a -> b) = 1 + n_arrows b

let xxx = n_arrows (int -> nat -> int)

let _ = assert (xxx == 2)
