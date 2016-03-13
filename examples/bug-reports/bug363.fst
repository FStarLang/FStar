module Bug363
type tt 
type Good : nat -> Type
type tpar (ps:nat) = m:tt{Good ps} 

val pstep: ps':nat -> pi:(tpar ps' * unit) -> Tot (tpar ps')
let pstep ps' pi  = MkTuple2._1 pi

let pstep_lemma (ps':nat) (pi:(tpar ps' * unit))  =  assert(pstep ps' pi = MkTuple2._1 pi)

