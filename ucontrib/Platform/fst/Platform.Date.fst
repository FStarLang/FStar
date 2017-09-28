module Platform.Date
assume new type dateTime : Type0
assume new type timeSpan : Type0

assume val now: unit -> EXT dateTime
assume val secondsFromDawn: unit -> EXT (n:nat{FStar.Bytes.repr_bytes n <= 4})
assume val newTimeSpan: int -> int -> int -> int -> Tot timeSpan
assume val addTimeSpan: dateTime -> timeSpan -> Tot dateTime
assume val greaterDateTime: dateTime -> dateTime -> Tot bool
