
open Prims
type prin =
| Alice
| Bob
| Charlie
| Dave
| Evelyn
| Fred

let is_Alice = (fun _discr_ -> (match (_discr_) with
| Alice -> begin
true
end
| _ -> begin
false
end))

let is_Bob = (fun _discr_ -> (match (_discr_) with
| Bob -> begin
true
end
| _ -> begin
false
end))

let is_Charlie = (fun _discr_ -> (match (_discr_) with
| Charlie -> begin
true
end
| _ -> begin
false
end))

let is_Dave = (fun _discr_ -> (match (_discr_) with
| Dave -> begin
true
end
| _ -> begin
false
end))

let is_Evelyn = (fun _discr_ -> (match (_discr_) with
| Evelyn -> begin
true
end
| _ -> begin
false
end))

let is_Fred = (fun _discr_ -> (match (_discr_) with
| Fred -> begin
true
end
| _ -> begin
false
end))

let p_cmp = (fun p1 p2 -> if (p1 = Alice) then begin
true
end else begin
if (p1 = Bob) then begin
(not ((p2 = Alice)))
end else begin
if (p1 = Charlie) then begin
(not (((p2 = Alice) || (p2 = Bob))))
end else begin
if (p1 = Dave) then begin
(not ((((p2 = Alice) || (p2 = Bob)) || (p2 = Charlie))))
end else begin
if (p1 = Evelyn) then begin
(not (((((p2 = Alice) || (p2 = Bob)) || (p2 = Charlie)) || (p2 = Dave))))
end else begin
(not ((((((p2 = Alice) || (p2 = Bob)) || (p2 = Charlie)) || (p2 = Dave)) || (p2 = Evelyn))))
end
end
end
end
end)

type eprins =
(prin, Prims.unit) FStar_OrdSet.ordset

type prins =
(prin, Prims.unit) FStar_OrdSet.ordset

let rec ps_cmp = (fun ps1 ps2 -> if ((FStar_OrdSet.size ((fun ps1 ps2 -> p_cmp) ps1 ps2) ps1) < (FStar_OrdSet.size ((fun ps1 ps2 -> p_cmp) ps1 ps2) ps2)) then begin
false
end else begin
if ((FStar_OrdSet.size ((fun ps1 ps2 -> p_cmp) ps1 ps2) ps1) > (FStar_OrdSet.size ((fun ps1 ps2 -> p_cmp) ps1 ps2) ps2)) then begin
true
end else begin
if ((ps1 = (FStar_OrdSet.empty ((fun ps1 ps2 -> p_cmp) ps1 ps2))) && (ps2 = (FStar_OrdSet.empty ((fun ps1 ps2 -> p_cmp) ps1 ps2)))) then begin
true
end else begin
(let _17_12 = ((FStar_OrdSet.choose ((fun ps1 ps2 -> p_cmp) ps1 ps2) ps1), (FStar_OrdSet.choose ((fun ps1 ps2 -> p_cmp) ps1 ps2) ps2))
in (match (_17_12) with
| (Some (p1), Some (p2)) -> begin
(let _17_15 = ((FStar_OrdSet.remove ((fun ps1 ps2 _17_12 p1 p2 -> p_cmp) ps1 ps2 _17_12 p1 p2) p1 ps1), (FStar_OrdSet.remove ((fun ps1 ps2 _17_12 p1 p2 -> p_cmp) ps1 ps2 _17_12 p1 p2) p2 ps2))
in (match (_17_15) with
| (ps1_rest, ps2_rest) -> begin
if (p1 = p2) then begin
(ps_cmp ps1_rest ps2_rest)
end else begin
(p_cmp p1 p2)
end
end))
end))
end
end
end)

let rec ps_cmp_antisymm = (fun ps1 ps2 -> ())

let rec ps_cmp_trans = (fun ps1 ps2 ps3 -> ())

let rec ps_cmp_total = (fun ps1 ps2 -> ())

let insert = (fun p ps -> (FStar_OrdSet.union ((fun p ps -> ((fun p ps -> p_cmp) p ps)) p ps) (FStar_OrdSet.singleton ((fun p ps -> ((fun p ps -> p_cmp) p ps)) p ps) p) ps))

let all_prins = (fun _17_59 -> (insert Alice (insert Bob (insert Charlie (insert Dave (insert Evelyn (insert Fred (FStar_OrdSet.empty ((fun _17_59 -> p_cmp) ())))))))))

let all_prins_superset_lemma = (fun _17_62 -> ())




