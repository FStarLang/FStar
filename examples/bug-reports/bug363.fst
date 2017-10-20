module Bug363

assume new type tt
assume new type good : nat -> Type
type tpar (ps:nat) = m:tt{good ps}

val pstep: ps':nat -> pi:(tpar ps' * unit) -> Tot (tpar ps')
let pstep ps' pi  = Mktuple2?._1 pi

let pstep_lemma (ps':nat) (pi:(tpar ps' * unit)) =  assert(pstep ps' pi == Mktuple2?._1 pi)
