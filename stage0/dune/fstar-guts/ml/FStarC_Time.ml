type time_of_day = float

let get_time_of_day () = BatUnix.gettimeofday()

let get_time_of_day_ms () = Z.of_int (int_of_float (get_time_of_day () *. 1000.0))

let get_file_last_modification_time f = (BatUnix.stat f).BatUnix.st_mtime

let is_before t1 t2 = compare t1 t2 < 0

let string_of_time_of_day = string_of_float
