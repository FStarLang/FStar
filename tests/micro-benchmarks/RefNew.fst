module RefNew
#push-options "--ext pretyping_axioms"
open FStar.Ref

let _ = assert (ref int =!= int)
