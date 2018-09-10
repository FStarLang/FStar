module FStar.Date
new
val dateTime: Type0
new
val timeSpan: Type0

val now: unit -> EXT dateTime
val secondsFromDawn: unit -> EXT (n: nat{n < pow2 32})
val newTimeSpan: int -> int -> int -> int -> Tot timeSpan
val addTimeSpan: dateTime -> timeSpan -> Tot dateTime
val greaterDateTime: dateTime -> dateTime -> Tot bool

