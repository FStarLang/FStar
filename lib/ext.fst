(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module FStar.FunctionalExtensionality
#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"

type efun (a:Type) (b:Type) = a -> Tot b

opaque type FEq (#a:Type) (#b:Type) (f:efun a b) (g:efun a b) =
  (forall x.{:pattern (f x) \/ (g x)} f x = g x)

assume Extensionality : forall (a:Type) (b:Type) (f: efun a b) (g: efun a b).
                        {:pattern FEq #a #b f g} FEq #a #b f g <==> f=g

end
