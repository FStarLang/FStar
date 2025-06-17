module Bug3865b

[@@PpxDerivingShow; no_auto_projectors]
type ast0_wf_typ : int -> Type =
  | WfTRewrite:
    (x1 : int) ->
    (x2 : int) ->
    ast0_wf_typ x1 ->
    ast0_wf_typ x2
