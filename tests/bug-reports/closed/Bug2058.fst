module Bug2058

type record1 = { field : string }
let r0 = { field = "aaa" }
type record2 = { field : list string }
let r1 = {field = ["aaa"]}

let r2 = Mkrecord1 "aaa"
let r3 = Mkrecord2 [ "aaa"; "bbb" ]
