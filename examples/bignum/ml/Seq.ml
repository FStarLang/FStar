type 'a seq = 'a array

let length = Array.length
let create = Array.make
let index = Array.get
let upd a i v = 
  Array.set a i v;
  a  
let append = Array.append
let slice a i j = Array.sub a i (j-i)
let print s =
  Array.iter (fun x -> print_string (string_of_int x); print_string " ") s;
  print_string "\n"
let copy = Array.copy
let lemma_create_len = (fun n i -> ())

let lemma_len_upd = (fun n v s -> ())

let lemma_len_append = (fun s1 s2 -> ())

let lemma_len_slice = (fun s i j -> ())

let lemma_index_create = (fun n v i -> ())

let lemma_index_upd1 = (fun n v s -> ())

let lemma_index_upd2 = (fun n v s i -> ())

let lemma_index_app1 = (fun s1 s2 i -> ())

let lemma_index_app2 = (fun s2 s2 i -> ())

let lemma_index_slice = (fun s i j k -> ())

let lemma_eq_intro = (fun s1 s2 -> ())

let lemma_eq_refl = (fun s1 s2 -> ())

let lemma_eq_elim = (fun s1 s2 -> ())
