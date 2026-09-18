module InitMiddle

let stored : FStar.UInt32.t = InitBase.sum ()

let read (_:unit) : FStar.UInt32.t = stored
