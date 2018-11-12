module B
open FStar.HyperStack.ST
open FStar.Buffer

let validate argc argv = FStar.UInt32.(argc >=^ 2ul)
