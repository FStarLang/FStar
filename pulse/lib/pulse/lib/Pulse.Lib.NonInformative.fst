module Pulse.Lib.NonInformative

open FStar.Ghost

instance non_informative_unit : non_informative unit = {
  reveal = (fun _ -> ());
}

// FIXME: are the annotations needed since there is no expected type on fields?
instance non_informative_prop : non_informative prop = {
  reveal = (fun p -> p) <: revealer prop;
}

instance non_informative_erased (a:Type) : non_informative (erased a) = {
  reveal = (fun e -> Ghost.reveal e) <: revealer (erased a);
}

instance non_informative_squash (a:Type) : non_informative (squash a) = {
  reveal = (fun e -> Ghost.reveal e) <: revealer (squash a);
}


// FIXME: some silly interactions between projector resolution,
// typeclasses, namespaces, coercions, etc, so we use the dictionaries
// explicitly.

instance non_informative_tuple2
  (a b : Type)
  (d1 : non_informative a)
  (d2 : non_informative b)
  : non_informative (a & b) = {
  reveal = (fun p -> (d1.reveal (Ghost.elift1 Mktuple2?._1 p),
                      d2.reveal (Ghost.elift1 Mktuple2?._2 p)));
}

instance non_informative_tuple3
  (a b c : Type)
  (d1 : non_informative a)
  (d2 : non_informative b)
  (d3 : non_informative c)
  : non_informative (a & b & c) = {
  reveal = (fun p -> (d1.reveal (Ghost.elift1 Mktuple3?._1 p),
                      d2.reveal (Ghost.elift1 Mktuple3?._2 p),
                      d3.reveal (Ghost.elift1 Mktuple3?._3 p)));
}

instance non_informative_tuple4
  (a b c d : Type)
  (d1 : non_informative a)
  (d2 : non_informative b)
  (d3 : non_informative c)
  (d4 : non_informative d)
  : non_informative (a & b & c & d) = {
  reveal = (fun p -> (d1.reveal (Ghost.elift1 Mktuple4?._1 p),
                      d2.reveal (Ghost.elift1 Mktuple4?._2 p),
                      d3.reveal (Ghost.elift1 Mktuple4?._3 p),
                      d4.reveal (Ghost.elift1 Mktuple4?._4 p)));
}

instance non_informative_tuple5
  (a b c d e : Type)
  (d1 : non_informative a)
  (d2 : non_informative b)
  (d3 : non_informative c)
  (d4 : non_informative d)
  (d5 : non_informative e)
  : non_informative (a & b & c & d & e) = {
  reveal = (fun p -> (d1.reveal (Ghost.elift1 Mktuple5?._1 p),
                      d2.reveal (Ghost.elift1 Mktuple5?._2 p),
                      d3.reveal (Ghost.elift1 Mktuple5?._3 p),
                      d4.reveal (Ghost.elift1 Mktuple5?._4 p),
                      d5.reveal (Ghost.elift1 Mktuple5?._5 p)));
}

instance non_informative_tuple6
  (a b c d e f : Type)
  (d1 : non_informative a)
  (d2 : non_informative b)
  (d3 : non_informative c)
  (d4 : non_informative d)
  (d5 : non_informative e)
  (d6 : non_informative f)
  : non_informative (a & b & c & d & e & f) = {
  reveal = (fun p -> (d1.reveal (Ghost.elift1 Mktuple6?._1 p),
                      d2.reveal (Ghost.elift1 Mktuple6?._2 p),
                      d3.reveal (Ghost.elift1 Mktuple6?._3 p),
                      d4.reveal (Ghost.elift1 Mktuple6?._4 p),
                      d5.reveal (Ghost.elift1 Mktuple6?._5 p),
                      d6.reveal (Ghost.elift1 Mktuple6?._6 p)));
}

instance non_informative_tuple7
  (a b c d e f g : Type)
  (d1 : non_informative a)
  (d2 : non_informative b)
  (d3 : non_informative c)
  (d4 : non_informative d)
  (d5 : non_informative e)
  (d6 : non_informative f)
  (d7 : non_informative g)
  : non_informative (a & b & c & d & e & f & g) = {
  reveal = (fun p -> (d1.reveal (Ghost.elift1 Mktuple7?._1 p),
                      d2.reveal (Ghost.elift1 Mktuple7?._2 p),
                      d3.reveal (Ghost.elift1 Mktuple7?._3 p),
                      d4.reveal (Ghost.elift1 Mktuple7?._4 p),
                      d5.reveal (Ghost.elift1 Mktuple7?._5 p),
                      d6.reveal (Ghost.elift1 Mktuple7?._6 p),
                      d7.reveal (Ghost.elift1 Mktuple7?._7 p)));
}
