module Even

open FStar.Tactics

type unat = | Z : unat | S : unat → unat
let rec nat2unary (n: nat) : Tot unat = if n = 0 then Z else S (nat2unary (n - 1))
type even : unat → Type = | Even_Z : even Z | Even_SS : #n: unat → even n → even (S (S n))

let prove_even () = compute (); ignore (repeat (fun () -> apply (`Even_SS))); apply (`Even_Z)

let even10 : even (normalize_term (nat2unary 10)) = synth prove_even
