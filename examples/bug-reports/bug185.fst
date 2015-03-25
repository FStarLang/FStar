module Bug

assume type data

type vk = data

type tag = data

opaque type verified : vk -> data -> Type
type vkey (p:(data -> Type)) = k:vk{verified k == p}

assume val verify: p:(data -> Type) -> v:vkey p -> d:data -> tag -> Tot (b:bool{b ==> p d})

assume val format : list data -> Tot data
assume val parse : d:data -> Tot (s : list data {format s = d})

opaque type certified (d:data)
assume Certified:
    (forall k. {:pattern (format [k])}
            certified (format [k]) <==> verified k == certified )

val validate: vkey certified -> list data -> unit
let rec validate vk0 chain =
    (match chain with
    | cert:: chain_tl ->
        (match parse cert with
        | [ ctxt; ctag ] ->
            (match parse ctxt with
            | [ sender; vk ] -> ()
            | [ vk ] -> if verify #certified vk0 ctxt ctag then
              (
(*               assert (verified vk == certified); magic() -- succeeds *)
(*               validate vk chain_tl -- fails*)
(*               assume (verified vk == certified); -- adding this makes the
                     verified it work, unless the assert is still
                     around, in which case that starts failing*)

                assert (verified vk == certified)
)
                 else ()
            | _ -> ())
        | _ -> ())
    | [] -> ())
