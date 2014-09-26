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
    | write (message : string).
  End Output.
End Log.

(** Events to read files. *)
Module File.
  (** Incoming events. *)
  Module Input.
    Inductive t : Set :=
    | read (file_name : string) (content : string)
      (** All the file content had been read. *).
  End Input.

  (** Generated events. *)
  Module Output.
    Inductive t : Set :=
    | read (file_name : string) (** Read all the content of a file. *).
  End Output.
End File.

(** Events for general system calls. *)
Module System.
  Module Output.
    Inductive t : Set :=
    | exit.
  End Output.
End System.

(** Events for the TCP client sockets. *)
Module TCPClientSocket.
  (** Identifier for a client socket (hopefully unique). *)
  Module Id.
    Require Import Coq.Numbers.Natural.Peano.NPeano.

    (** An integer. *)
    Inductive t : Set :=
    | new : nat -> t.

    (** Test equality. *)
    Definition eqb (id1 id2 : t) : bool :=
      match (id1, id2) with
      | (new id1, new id2) => Nat.eqb id1 id2
      end.
  End Id.

  (** Incoming events. *)
  Module Input.
    Inductive t : Set :=
    | accepted (id : Id.t)
    | read (id : Id.t) (content : string).
  End Input.

  (** Generated events. *)
  Module Output.
    Inductive t : Set :=
    | write (id : Id.t) (message : string)
    | close (id : Id.t).
  End Output.
End TCPClientSocket.

(** Events for the TCP server sockets. *)
Module TCPServerSocket.
  (** Identifier for a server socket (hopefully unique). *)
  Module Id.
    (** An integer. *)
    Inductive t : Set :=
    | new : nat -> t.
  End Id.

  (** Incoming events. *)
  Module Input.
    Inductive t : Set :=
    | bound (id : Id.t).
  End Input.

  (** Generated events. *)
  Module Output.
    Inductive t : Set :=
    | bind (port : nat)
    | close (id : Id.t).
  End Output.
End TCPServerSocket.

(** Incoming events. *)
Module Input.
  Inductive t : Set :=
  | file : File.Input.t -> t
  | client_socket : TCPClientSocket.Input.t -> t
  | server_socket : TCPServerSocket.Input.t -> t.
End Input.

(** Generated events. *)
Module Output.
  Inductive t : Set :=
  | log : Log.Output.t -> t
  | file : File.Output.t -> t
  | system : System.Output.t -> t
  | client_socket : TCPClientSocket.Output.t -> t
  | server_socket : TCPServerSocket.Output.t -> t.
End Output.