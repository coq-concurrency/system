(** Experiments for a TCP sockets API. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Computation.

Import ListNotations.
Import C.Notations.

Module Address.
  Definition t : Type := (nat * nat * nat * nat) % type.
End Address.

Module ServerId.
  Definition t : Type := nat.
End ServerId.

Module ConnectionId.
  Definition t : Type := nat.
End ConnectionId.

Module Input.
  Inductive t : Type :=
  | bound : ServerId.t -> t
  | accepted : ConnectionId.t -> t
  | read : ConnectionId.t -> string -> t.
End Input.

Module Output.
  Inductive t : Type :=
  | bind : Address.t -> nat -> t
  | write : ConnectionId.t -> string -> t
  | close_server : ServerId.t -> t
  | close_connection : ConnectionId.t -> t.
End Output.