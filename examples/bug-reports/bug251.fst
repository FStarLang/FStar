module Bug251
let t = magic() // GM: had to change this one to magic() after making admit() return a unit
let lemma_1 () = admit()
let lemma_2 () = lemma_1()
