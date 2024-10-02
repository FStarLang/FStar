module Part2.STInt

//SNIPPET_START: st$
let st a = int -> a & int
//SNIPPET_END: st$

//SNIPPET_START: read_and_increment_v0$
let read_and_increment_v0
  : st int
  = fun s0 -> s0, s0 + 1
//SNIPPET_END: read_and_increment_v0$

//SNIPPET_START: inc_twice_v0$
let inc_twice_v0
  : st int
  = fun s0 ->
      let x, s1 = read_and_increment_v0 s0 in
      let _, s2 = read_and_increment_v0 s1 in
      x, s2
//SNIPPET_END: inc_twice_v0$

//SNIPPET_START: inc_twice_buggy$
let inc_twice_buggy
  : st int
  = fun s0 ->
      let x, s1 = read_and_increment_v0 s0 in
      let _, s2 = read_and_increment_v0 s0 in
      x, s2
//SNIPPET_END: inc_twice_buggy$

//SNIPPET_START: read$
let read
  : st int
  = fun s -> s, s
//SNIPPET_END: read$

//SNIPPET_START: write$
let write (s1:int)
  : st unit
  = fun _ -> (), s1
//SNIPPET_END: write$

//SNIPPET_START: bind$
let bind #a #b
         (f: st a)
         (g: a -> st b)
  : st b
  = fun s0 ->
      let x, s1 = f s0 in
      g x s1
//SNIPPET_END: bind$

//SNIPPET_START: return$
let return #a (x:a)
  : st a
  = fun s -> x, s
//SNIPPET_END: return$

//SNIPPET_START: read_and_increment_v1$
let read_and_increment_v1 : st int = 
  bind read (fun x -> 
  bind (write (x + 1)) (fun _ -> 
  return x))
//SNIPPET_END: read_and_increment_v1$

//SNIPPET_START: let!$
let (let!) = bind
//SNIPPET_END: let!$

//SNIPPET_START: read_and_increment$
let read_and_increment : st int =
  let! x = read in
  write (x + 1) ;!
  return x
//SNIPPET_END: read_and_increment$

//SNIPPET_START: inc_twice$
let inc_twice : st int = 
  let! x = read_and_increment in
  read_and_increment ;!
  return x
//SNIPPET_END: inc_twice$

//SNIPPET_START: monad_laws$
let feq #a #b (f g : a -> b) = forall x. f x == g x
let left_identity #a #b (x:a) (g: a -> st b)
  : Lemma ((let! v = return x in g v) `feq` g x)
  = ()
let right_identity #a (f:st a)
  : Lemma ((let! x = f in return x) `feq` f)
  = ()
let associativity #a #b #c (f1:st a) (f2:a -> st b) (f3:b -> st c)
  : Lemma ((let! x = f1 in let! y = f2 x in f3 y) `feq`
           (let! y = (let! x = f1 in f2 x) in f3 y))
  = ()
//SNIPPET_END: monad_laws$


//SNIPPET_START: bind_buggy$
let bind_buggy #a #b
               (f: st a)
               (g: a -> st b)
  : st b
  = fun s0 ->
      let x, s1 = f s0 in
      g x s0
[@@expect_failure]
let right_identity_fail #a (f:st a)
  : Lemma (bind_buggy f return `feq` f)
  = ()
//SNIPPET_END: bind_buggy$

//SNIPPET_START: action_laws$
let redundant_read_elim ()
  : Lemma ((read;! read) `feq` read)
  = ()

let redundant_write_elim (x y:int)
  : Lemma ((write x ;! write y) `feq` write y)
  = ()

let read_write_noop ()
  : Lemma ((let! x = read in write x) `feq` return ())
  = ()
//SNIPPET_END: action_laws$

