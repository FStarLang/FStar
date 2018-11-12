module Bug1443d

noeq type ins 'ins_typ = {
  eval_ins : 'ins_typ -> unit;
  ins_to_string : 'int_typ -> string
}

noeq type add64 't1 't2 = {
  dst: 't1;
  src: 't2
}

assume val eval_add64 : add64 't1 't2 ->  unit

assume val add64_to_string : add64 't1 't2 -> string

[@(expect_failure [66])]
let add64_ins (#t1:Type)(#t2:Type) : ins (add64 t1 t2) = {
  eval_ins = eval_add64;
  ins_to_string = add64_to_string
}
