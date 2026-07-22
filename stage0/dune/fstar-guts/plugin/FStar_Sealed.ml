type 'a sealed = 'a
let seal x = x
let map_seal s f = f s
let bind_seal s f = f s
