type time_ns = int64

let now_ns () = Mtime_clock.now_ns()
let diff_ns t1 t2 =
  Z.of_int (Int64.to_int (Int64.sub t2 t1))
let diff_ms t1 t2 = Z.div (diff_ns t1 t2) (Z.of_int 1000000)
let record_ns f =
    let start = now_ns () in
    let res = f () in
    let elapsed = diff_ns start (now_ns()) in
    res, elapsed
let record_ms f =
    let res, ns = record_ns f in
    res, Z.div ns (Z.of_int 1000000)
