(** Basic type and event definitions. *)
Require Import Coq.Strings.String.

(** Events to log data. *)
Module Log.
  Module Output.
    Inductive t : Type :=
    | write : string -> t.
  End Output.
End Log.

(** Events to read files. *)
Module File.
  (** The name of a file. *)
  Module Name.
    (** A file name is a path and a base name. *)
    Record t : Type := {
      path : list string;
      name : string }.

    (** Convert a file name to a single string. *)
    Definition to_string (file_name : t) : string :=
      name file_name.
  End Name.

  (** Incoming events. *)
  Module Input.
    Inductive t : Type :=
    | read : string -> t (** The file content had been read. *).
  End Input.

  (** Generated events. *)
  Module Output.
    Inductive t : Type :=
    | read : Name.t -> t (** Read all the content of a file. *).
  End Output.
End File.

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
    | close_connection : ConnectionId.t -> t.
  End Output.
End TCPServerSocket.

Module Input.
  Inductive t : Type :=
  | file : File.Input.t -> t
  | socket : TCPServerSocket.Input.t -> t.
End Input.

Module Output.
  Inductive t : Type :=
  | log : Log.Output.t -> t
  | file : File.Output.t -> t
  | socket : TCPServerSocket.Output.t -> t.
End Output.