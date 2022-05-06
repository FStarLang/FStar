module UInt32

let t = n:nat { n <= pow2 32 - 1}

let v (x:t) = x
let u (x:u32_nat) = x

let uv_inv x = ()
let vu_inv x = ()

let add_mod a b = (a + b) % pow2 32
let sub_mod a b = (a - b) % pow2 32

let add a b = a + b
let sub a b = a - b

let lt (a:t) (b:t) = v a < v b
