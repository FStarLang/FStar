module Bug2094a

val split: #a:Type -> #b:Type -> list (a * b) -> Tot (list a * list b)
let rec split l = match l with
    | [] -> ([],[])
    | (hd1,hd2)::tl ->
       let (tl1,tl2) = split tl in
       (hd1::tl1,hd2::tl2)

let unzip = split

val tac : list (nat & nat) -> Tot (list nat & list nat)
let tac ls = unzip ls
