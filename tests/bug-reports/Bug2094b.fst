module Bug2094b

val split: #a:Type -> list a -> Tot (list a)
let split l = l

let unzip = fun #a -> split #a

val tac : list nat -> Tot (list nat)
let tac ls = unzip ls
