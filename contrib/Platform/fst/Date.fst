module Platform.Date
type dateTime
type TimeSpan
assume val now: unit -> dateTime
assume val secondsFromDawn: unit -> n:nat{Bytes.repr_bytes n <= 4}  
assume val newTimeSpan: int -> int -> int -> int -> TimeSpan
assume val addTimeSpan: dateTime -> TimeSpan -> dateTime
assume val greaterDateTime: dateTime -> dateTime -> bool
