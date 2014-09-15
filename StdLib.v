(** The standard library. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Computation.
Require Import Log.
Require Import Socket.

Import ListNotations.
Import C.Notations.

Module Input.
  Inductive t : Type :=
  | socket : Socket.Input.t -> t.
End Input.

Module Output.
  Inductive t : Type :=
  | log : Log.Output.t -> t
  | socket : Socket.Output.t -> t.
End Output.

Definition bind {sig : Signature.t} (address : Socket.Address.t) (port : nat)
  : C.t sig Output.t unit :=
  C.write (Output.socket (Socket.Output.bind address port)).