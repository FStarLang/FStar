module Bug186

noeq type valid : int -> Type =
  | VForall     : p:(int -> Tot int) ->
                  f: valid (p 67) ->
                  valid 42

val hoare_consequence : valid 42 -> Tot unit
let hoare_consequence v =
  let VForall p v' = v in
(*  ignore (fpp' 75) -- this causes bogus "patterns are incomplete" *)
  assert (VForall? (* this solves it: #(p 67) *) v')
    (* BUG: this makes F* explode: Impossible: Typ_unknown *)
