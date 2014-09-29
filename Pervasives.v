(** Basic type and event definitions. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import String.

Import ListNotations.
Open Local Scope string.

(** Events to log data. *)
Module Log.
  Module Output.
    Inductive t : Set :=
    | Write (message : string).
  End Output.
End Log.

(** Events to read files. *)
Module File.
  (** Incoming events. *)
  Module Input.
    Inductive t : Set :=
    | Read (file_name : string) (content : string)
      (** All the file content had been read. *).
  End Input.

  (** Generated events. *)
  Module Output.
    Inductive t : Set :=
    | Read (file_name : string) (** Read all the content of a file. *).
  End Output.
End File.

(** Events for the TCP client sockets. *)
Module TCPClientSocket.
  (** Identifier for a client socket (hopefully unique). *)
  Module Id.
    Require Import Coq.Numbers.Natural.Peano.NPeano.

    (** An integer. *)
    Inductive t : Set :=
    | New : nat -> t.

    (** Test equality. *)
    Definition eqb (id1 id2 : t) : bool :=
      match (id1, id2) with
      | (New id1, New id2) => Nat.eqb id1 id2
      end.
  End Id.

  (** Incoming events. *)
  Module Input.
    Inductive t : Set :=
    | Accepted (id : Id.t)
    | Read (id : Id.t) (content : string).
  End Input.

  (** Generated events. *)
  Module Output.
    Inductive t : Set :=
    | Write (id : Id.t) (message : string)
    | Close (id : Id.t).
  End Output.
End TCPClientSocket.

(** Events for the TCP server sockets. *)
Module TCPServerSocket.
  (** Identifier for a server socket (hopefully unique). *)
  Module Id.
    (** An integer. *)
    Inductive t : Set :=
    | New : nat -> t.
  End Id.

  (** Incoming events. *)
  Module Input.
    Inductive t : Set :=
    | Bound (id : Id.t).
  End Input.

  (** Generated events. *)
  Module Output.
    Inductive t : Set :=
    | Bind (port : nat)
    | Close (id : Id.t).
  End Output.
End TCPServerSocket.

(** Incoming events. *)
Module Input.
  Inductive t : Set :=
  | File : File.Input.t -> t
  | ClientSocket : TCPClientSocket.Input.t -> t
  | ServerSocket : TCPServerSocket.Input.t -> t.
End Input.

(** Generated events. *)
Module Output.
  Inductive t : Set :=
  | Log : Log.Output.t -> t
  | File : File.Output.t -> t
  | ClientSocket : TCPClientSocket.Output.t -> t
  | ServerSocket : TCPServerSocket.Output.t -> t.
End Output.