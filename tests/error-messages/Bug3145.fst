module Bug3145

// Issue 3145 was about mismatches between * and &.
// We no longer use * for tuples.

let t1 = (int & int) & int
let t2 = int & (int & int)
let t3 = int & int & int
