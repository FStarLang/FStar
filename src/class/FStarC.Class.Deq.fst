module FStarC.Class.Deq

open FStarC.Effect

let (<>?) x y = not (x =? y)

instance deq_int : deq int = {
   (=?) = (fun x y -> x = y);
}

instance deq_bool : deq bool = {
   (=?) = (fun x y -> x = y);
}

instance deq_unit : deq unit = {
   (=?) = (fun x y -> true);
}

instance deq_string : deq string = {
   (=?) = (fun x y -> x = y);
}

instance deq_option #a (_ : deq a) : Tot (deq (option a)) = {
   (=?) = (fun x y -> match x, y with
           | None, None -> true
           | Some x, Some y -> x =? y
           | _, _ -> false)
}

let rec eqList (#a : Type) (eq : deq a) (xs : list a) (ys : list a) : bool =
  match xs, ys with
  | [], [] -> true
  | x::xs, y::ys -> x =? y && eqList #a eq xs ys
  | _, _ -> false

instance deq_list #a (d : deq a) : Tot (deq (list a)) = {
   (=?) = eqList d
}

instance deq_either #a #b (d1 : deq a) (d2 : deq b) : Tot (deq (either a b)) = {
   (=?) = (fun x y -> match x, y with
           | Inl x, Inl y -> x =? y
           | Inr x, Inr y -> x =? y
           | _, _ -> false)
}

instance deq_tuple2 #a #b (d1 : deq a) (d2 : deq b) : Tot (deq (a & b)) = {
   (=?) = (fun (x1, x2) (y1, y2) -> x1 =? y1 && x2 =? y2)
}

instance deq_tuple3 #a #b #c (d1 : deq a) (d2 : deq b) (d3 : deq c) : Tot (deq (a & b & c)) = {
   (=?) = (fun (x1, x2, x3) (y1, y2, y3) -> x1 =? y1 && x2 =? y2 && x3 =? y3)
}

instance deq_tuple4 #a #b #c #d (d1 : deq a) (d2 : deq b) (d3 : deq c) (d4 : deq d) : Tot (deq (a & b & c & d)) = {
   (=?) = (fun (x1, x2, x3, x4) (y1, y2, y3, y4) -> x1 =? y1 && x2 =? y2 && x3 =? y3 && x4 =? y4)
}

instance deq_tuple5 #a #b #c #d #e (d1 : deq a) (d2 : deq b) (d3 : deq c) (d4 : deq d) (d5 : deq e) : Tot (deq (a & b & c & d & e)) = {
   (=?) = (fun (x1, x2, x3, x4, x5) (y1, y2, y3, y4, y5) -> x1 =? y1 && x2 =? y2 && x3 =? y3 && x4 =? y4 && x5 =? y5)
}

instance deq_tuple6 #a #b #c #d #e #f (d1 : deq a) (d2 : deq b) (d3 : deq c) (d4 : deq d) (d5 : deq e) (d6 : deq f) : Tot (deq (a & b & c & d & e & f)) = {
   (=?) = (fun (x1, x2, x3, x4, x5, x6) (y1, y2, y3, y4, y5, y6) -> x1 =? y1 && x2 =? y2 && x3 =? y3 && x4 =? y4 && x5 =? y5 && x6 =? y6)
}
