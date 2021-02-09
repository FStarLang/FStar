module Bug2193

#set-options "--lax"

type foo: Type u#m = | FOO

let i (n: nat): Tot unit (decreases FOO)
  = admit () 

let bar (t:Type u#n): Type0 = True
let rec f (n: nat): Tot unit (decreases bar)
  = if n=0 then () else ()
