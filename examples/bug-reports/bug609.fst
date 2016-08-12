module Bug609

let add' = let x = op_Addition in assert (x 1 2 = 3)

let add'' = let x = (+) in assert (x 1 2 = 3)

#set-options "--initial_fuel 10 --initial_ifuel 10"
let test = assert (List.Tot.fold_left (+) 0 [1;2;3] = 6)
