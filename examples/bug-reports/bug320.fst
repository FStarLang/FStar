module Bug320

type r (#a:nat) = x:int { x < a }
type s (a:nat) = { x:r #a; }
type t (#a:nat) = s a
let foo: t = { x = 0; }
