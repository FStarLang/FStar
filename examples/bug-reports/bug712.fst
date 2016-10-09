module Bug712

inline let s = int -> Tot int
let r = f:s{True}

let app0 (m : r) = m 0
