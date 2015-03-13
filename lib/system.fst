module System
assume type Object

module System.IO
assume type TextWriter

module System.Text
assume type StringBuilder

module System.Diagnostics
assume type Process

module System.Collections.Generic
assume type HashSet: Type -> Type

module System.Threading.Thread
assume val Sleep: int -> unit

module System.Threading.Monitor
assume val Enter: 'a -> unit
assume val Exit: 'a -> unit

module Collections
assume type Set: Type -> Type
