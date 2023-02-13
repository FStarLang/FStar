module CoreEqualityGuard
open FStar.Squash
assume
val a : Type0

assume
val b (x:a) : Type0

assume
val r_b (x:a) (y z:b x) : Type0

let dsnd #a (#b: a -> Type) (x: dtuple2 a b) : b (dfst x) = dsnd x

// #push-options "--debug CoreEqualityGuard --debug_level SMTQuery,Rel"
// let test (t1 t2 : dtuple2 a b)
//          (p: squash (dfst t1 == dfst t2))
//   : b (dfst t1)
//   = dsnd t2
  

#push-options "--debug CoreEqualityGuard --debug_level Core"

let test (t1 t2 : dtuple2 a b)
         (p: (dfst t1 == dfst t2 /\
             r_b (dfst t1) (dsnd t1) (dsnd t2)))
    : squash trivial
    = bind_squash #(pair (dfst t1 == dfst t2) (r_b (dfst t1) (dsnd t1) (dsnd t2))) #trivial p (fun p -> 
        let Pair l r = p in return_squash T)
