module Bug1130

val bug: FStar.UInt8.byte -> bool
let bug = function
    | 0uy -> true
    | _ -> false
