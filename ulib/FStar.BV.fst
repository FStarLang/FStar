module FStar.BV

module U = FStar.UInt
module B = FStar.BitVector

let bv_t (n : nat) = B.bv_t n

let logand_vec = B.logand_vec
let logxor_vec = B.logxor_vec
let logor_vec = B.logor_vec
let lognot_vec = B.lognot_vec

(*TODO: specify index functions? *)
let shift_left_vec = B.shift_left_vec
let shift_right_vec = B.shift_right_vec

let to_vec = U.to_vec
let from_vec = U.from_vec

let to_vec_lemma_1 = U.to_vec_lemma_1
let to_vec_lemma_2 = U.to_vec_lemma_2

let div_vec #n a b = 
    U.div_size #n (from_vec #n a) (from_vec #n b);
    to_vec #n (U.div #n (from_vec #n a) (from_vec #n b))    
let mod_vec #n a b = 
    U.div_size #n (from_vec #n a) (from_vec #n b);
    to_vec #n (U.mod #n (from_vec #n a) (from_vec #n b))


let inverse_vec_lemma = U.inverse_vec_lemma
let inverse_num_lemma = U.inverse_num_lemma
