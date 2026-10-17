(* Model implementation of FStar.Date: verified, but never extracted (the real implementation is native). *)
module FStar.Date

type dateTime = | DateTime : seconds:int -> dateTime
type timeSpan = | TimeSpan : seconds:int -> timeSpan

let now () = DateTime 0
let secondsFromDawn () = 0
let newTimeSpan h m s ms = TimeSpan (3600 * h + 60 * m + s)
let addTimeSpan d t = DateTime (DateTime?.seconds d + TimeSpan?.seconds t)
let greaterDateTime d1 d2 = DateTime?.seconds d1 > DateTime?.seconds d2
