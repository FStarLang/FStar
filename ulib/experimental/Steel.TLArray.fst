module Steel.TLArray

let t a = list a

let v x = G.hide x
let length x = L.length x

let create l = l
let get x i = L.index x (U32.v i)
