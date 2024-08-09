type nonrec 'a array = 'a array 

type uint32 = FStar_UInt32.uint32
                          
let create len init = Array.make init len
let index x i = Array.get x i
let upd x i = Array.set x i
let length x = Array.length x
let swap x i j = let xi = index x i in
                 upd x i (index x j);
                 upd x j xi
let copy x = Array.copy
let blit a ai b bi len = Array.blit a ai b bi len
let sub s i len = Array.sub s i len
