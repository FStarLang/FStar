module Bug185

////////////////////////////////////////////////////////////////////////////////
assume val a_data : Type0
let a_vk = a_data
let a_vkey (u:unit) = x:a_vk{x==x}
val a_validate: a_data -> a_vkey ()
let a_validate chain = chain
//////////////////////////////////////////////////////////////////////////////////////////

assume type data
assume HasEq_data: hasEq data

type vk = data

type tag = data

assume new type verified : vk -> data -> Type
type vkey (p:(data -> Type)) = k:vk{verified k == p}

assume val verify: p:(data -> Type) -> v:vkey p -> d:data -> tag -> Tot (b:bool{b ==> p d})

assume val format : list data -> Tot data
assume val parse : d:data -> Tot (s : list data {format s = d})

assume new type certified (d:data)
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
            | [ vk ] -> if verify certified vk0 ctxt ctag then
              (
               assert (verified vk == certified);
               assume (verified vk == certified);
               validate vk chain_tl
              )
                 else ()
            | _ -> ())
        | _ -> ())
    | [] -> ())
