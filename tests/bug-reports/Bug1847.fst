module Bug1847

module F = FStar.FunctionalExtensionality

let t () : Type0 = F.restricted_t unit (fun _ -> unit)

assume val get_t (_:unit) : Tot (t ())

let test () = get_t () ()
