module Bug186

type valid : int -> Type =
  | VForall     : #p:(int -> Tot int) -> (* non-inferrable *)
                  f: (x:int -> Tot (valid (p x))) ->
                  valid 42

val hoare_consequence : valid 42 -> Tot unit
let hoare_consequence v =
  let VForall #p fpp' = v in (* #p here doesn't change anything *)
(*  ignore (fpp' 75) -- this causes bogus "patterns are incomplete" *)
  assert (is_VForall (fpp' 75))
    (* BUG: this makes F* explode: Impossible: Typ_unknown *)
