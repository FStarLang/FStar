#light "off"

module FStar.Common
open FStar.All
val try_convert_file_name_to_mixed: (string -> ML<string>)
val snapshot : (push: 'a -> 'b) -> (stackref: ref<list<'c>>) -> (arg: 'a) -> (int * 'b)
val rollback : (pop: unit -> 'a) -> (stackref: ref<list<'c>>) -> (depth: option<int>) -> 'a
