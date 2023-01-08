module SetClient

open SimplifiedFStarSet

let ( ^: ) (#a:eqtype) (x:a) (s:set a) : set a = union (singleton x) s

let _ = assert (not (mem 0 (1 ^: 2 ^: 3 ^: 4 ^: 5 ^: empty)))

assume
val mmem_union (#a:eqtype) (x:a) (s1 s2:set a)
  : Lemma
    (ensures (mem x (union s1 s2) == (mem x s1 || mem x s2)))
    [SMTPat (mem x s1); SMTPat (mem x s2)]

#push-options "--query_stats --fuel 0 --ifuel 0"
#restart-solver
let _ = assert (not (mem 0 (1 ^: empty)))



(*

let t = 10 ^: 20 ^: 30 ^: 40 ^: 50 ^: 60 ^: 70 ^: 80 ^: 90 ^: 100 ^: 
        11 ^: 21 ^: 31 ^: 41 ^: 50 ^: 60 ^: 70 ^: 80 ^: 90 ^: 100 ^: 
        12 ^: 22 ^: 32 ^: 42 ^: 50 ^: 60 ^: 70 ^: 80 ^: 90 ^: 100 ^: 
        13 ^: 23 ^: 33 ^: 43 ^: 50 ^: 60 ^: 70 ^: 80 ^: 90 ^: 100 ^: 
        14 ^: 24 ^: 34 ^: 44 ^: 50 ^: 60 ^: 70 ^: 80 ^: 90 ^: 100 ^: 
        empty

let _ = assert (not (mem 0 t))
*)
