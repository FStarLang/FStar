module Index

#push-options "--smtencoding.encode_string true"

open FStar.String

let hello = "hello"

val hello_index_0: unit -> Lemma (index hello 0 = '0')
let hello_index_0 () = ()
