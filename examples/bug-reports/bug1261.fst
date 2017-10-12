module Bug1261

let good : (t1 : int & (t2: int { t1 > t2 } )) =
    (| 2, 1 |)

let bad : (t1 : int & (t2: int { t1 > t2 } )) =
    (fun _ -> (| 2, 1 |)) ()
