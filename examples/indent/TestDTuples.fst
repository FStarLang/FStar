module TestDTuples

(* cf. issue #1945
 * ideally, we would also compare the output of --dump_module TestDTuples
 * to check that it doesn't regress *)

type box a = | Box : a -> box a

let mkBox = Box
let mkdtuple2 = Mkdtuple2
let mktuple2 = Mktuple2

let l_t_0 = [( 2+2, 1 )]
let l_t_1 = [Mktuple2 (2+2) 1]
let l_t_2 = Cons ( 2+2, 1 ) Nil
let l_t_3 = Cons #_ ( 2+2, 1 ) (Nil #_)
let l_t_4 = Cons (Mktuple2 (2+2) 1) Nil
let l_t_5 = Cons (Mktuple2 #_ #_ (2+2) 1) Nil
let l_t_6 = Cons #_ (Mktuple2 #_ #_ (2+2) 1) (Nil #_)

let l_d_0 = [(| 2+2, 1 |)]
let l_d_1 = [Mkdtuple2 (2+2) 1]
let l_d_2 = Cons (| 2+2, 1 |) Nil
let l_d_3 = Cons #_ (| 2+2, 1 |) (Nil #_)
let l_d_4 = Cons (Mkdtuple2 (2+2) 1) Nil
let l_d_5 = Cons (Mkdtuple2 #_ #_ (2+2) 1) Nil
let l_d_6 = Cons #_ (Mkdtuple2 #_ #_ (2+2) 1) (Nil #_)

let b_t_1 = Box ( 2+2, 1 )
let b_t_2 = Box #_ ( 2+2, 1 )
let b_t_3 = Box (Mktuple2 (2+2) 1)
let b_t_4 = Box (Mktuple2 #_ #_ (2+2) 1)
let b_t_5 = Box #_ (Mktuple2 #_ #_ (2+2) 1)

let b_d_1 = Box (| 2+2, 1 |)
let b_d_2 = Box #_ (| 2+2, 1 |)
let b_d_3 = Box (Mkdtuple2 (2+2) 1)
let b_d_4 = Box (Mkdtuple2 #_ #_ (2+2) 1)
let b_d_5 = Box #_ (Mkdtuple2 #_ #_ (2+2) 1)
