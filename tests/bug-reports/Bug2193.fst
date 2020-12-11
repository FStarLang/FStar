module Bug2193

#set-options "--lax"

type foo: Type u#m = | FOO

let i (n: nat): Tot unit (decreases FOO)
  = admit () 
