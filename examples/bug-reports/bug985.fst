module Bug985

let c (w:(z:(unit * unit) & unit) * unit) : unit =
  let w1, w2 = w in
  match w1, w2 with
  | (|(_,_), _|), _ -> ()
