
module JSUnit.Tuples

let f (a, b, c, d) = (a+b)/(c+d)
let x = f (1, 3, 2, 2)

let a = ("a", (0,1), 1)

let d = match (a,a) with
| (("a", p, b),(_,_,y)) when (snd p <> y) -> 1
| ((_,(0,x),_),(_,_,y)) when (x=y) -> 2
| _ -> 3

let nil =
        JS.utest "TupleArgument" x 1 ;
        JS.utest "TuplePattern" d 2

