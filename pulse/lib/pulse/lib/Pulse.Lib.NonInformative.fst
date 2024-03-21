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
