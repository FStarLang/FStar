module Bug2269

open FStar.Tactics

let a: string =
  _ by (let dtup = (|1, 4|) = (|1, 4|) in // does not reduce
        let  tup = ( 1, 4 ) = ( 1, 4 ) in // reduces to true
        let f t = norm_term [primops] (quote t) in 
        let s0 = term_to_string (f dtup) in
        let s1 = term_to_string (f  tup) in
        let s = s0 ^ " and " ^ s1 in
        exact (quote s)
       )

let _ = assert (a == "true and true")

