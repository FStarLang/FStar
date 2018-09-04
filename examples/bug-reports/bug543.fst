module Bug543

type range = r:(int * int) { fst r <= snd r }
type wider (r1:range) (r2:range) = fst r1 <= fst r2 /\ snd r2 <= snd r1
type within (n:int) (r:range) = fst r <= n /\ n <= snd r
type rint (r:range) = n:int {fst r <= n /\ n <= snd r}

let u:range = (0,1)
assume val r : (r:range{wider r u})

val f: n:int {within n u} -> m:int {within m r}
let f n = n

val g: rint u -> rint r

//This fails: (NS: not any more)
let g n = n

//This also works
let g' n = let m:int = n in m
