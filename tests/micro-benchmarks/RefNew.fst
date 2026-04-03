module RefNew
#push-options "--ext pretyping_axioms"
open FStar.All

let _ = assert (ref int =!= int)
