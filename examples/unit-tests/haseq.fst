module Haseq

type step : a:Type -> Type =
  | SApp1 : step nat

