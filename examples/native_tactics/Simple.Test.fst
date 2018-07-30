module Simple.Test
open Simple
#set-options "--use_two_phase_tc false"
type t = | This | That
let test0 = assert_norm (id 1000000 = 1000000)
let test1 = assert_norm (poly_id 1000000 This = This)
let test2 = assert_norm (mk_n_list 10 This = [This;This;This;This;This;This;This;This;This;This])
let test3 = assert_norm (poly_list_id (mk_n_list 100000 This) = mk_n_list 100000 This)
let test4 = assert_norm (eq_int_list (poly_list_id (mk_n_list 100000 0))
                                     (mk_n_list 100000 0))
