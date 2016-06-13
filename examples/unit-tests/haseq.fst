module Haseq

type step : a:Type -> Type -> a -> Type =
  | SApp1 : step nat int 0

