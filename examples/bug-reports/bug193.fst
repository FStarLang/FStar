module Bug193

type form =
| FTrue   : form
| FImpl   : form -> form -> form

type deduce : form -> Type =
  | DImplIntro :
             #f1:form ->
             #f2:form ->
             (deduce f1 -> Tot (deduce f2)) -> (* <-- meta level implication *)
             deduce (FImpl f1 f2)

type pred = heap -> Tot form

val wlp_sound : q:pred -> Tot unit
let rec wlp_sound q =
  ignore(fun h -> (DImplIntro (*#FTrue #FTrue*) (fun pq -> pq)))
