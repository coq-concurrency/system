(** Basic type and event definitions. *)
Require Import Coq.Strings.String.

Module Log.
  Module Output.
    Inductive t : Type :=
    | write : string -> t.
  End Output.
End Log.

Module TCPServerSocket.
  Module Id.
    Inductive t : Type :=
    | new : nat -> t.
  End Id.

  Module ConnectionId.
    Inductive t : Type :=
    | new : nat -> t.
  End ConnectionId.

  Module Input.
    Inductive t : Type :=
    | bound : Id.t -> t
    | accepted : ConnectionId.t -> t
    | read : ConnectionId.t -> string -> t.
  End Input.

  Module Output.
    Inductive t : Type :=
    | bind : nat -> t
    | write : ConnectionId.t -> string -> t
    | close_connection : ConnectionId.t -> t
    | close_server : Id.t -> t.
  End Output.
End TCPServerSocket.

Module Input.
  Inductive t : Type :=
  | socket : TCPServerSocket.Input.t -> t.
End Input.

Module Output.
  Inductive t : Type :=
  | log : Log.Output.t -> t
  | socket : TCPServerSocket.Output.t -> t.
End Output.