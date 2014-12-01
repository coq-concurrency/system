(** Events which define the API to the system. *)
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Coq.PArith.PArith.
Require Import ListString.All.

Import ListNotations.
Local Open Scope type.

(** The id of a server socket. *)
Module ServerSocketId.
  (** A socket id is a natural number. *)
  Inductive t : Set :=
  | New : N -> t.
End ServerSocketId.

(** The id of a client socket. *)
Module ClientSocketId.
  (** A socket id is a natural number. *)
  Inductive t : Set :=
  | New : N -> t.
End ClientSocketId.

(** The kind of commands. *)
Module Command.
  (** The list of commands. *)
  Inductive t : Type :=
  | Read
  | Write
  | FileRead
  | ServerSocketBind | ServerSocketAccept
  | ClientSocketRead | ClientSocketWrite | ClientSocketClose
  | Time.

  (** The type of the parameters of a request. *)
  Definition request (command : t) : Type :=
    match command with
    | Read => unit
    | Write => LString.t
    | FileRead => LString.t
    | ServerSocketBind => N
    | ServerSocketAccept => ServerSocketId.t
    | ClientSocketRead => ClientSocketId.t
    | ClientSocketWrite => ClientSocketId.t * LString.t
    | ClientSocketClose => ClientSocketId.t
    | Time => unit
    end.

  (** The type of the parameters of an answer. *)
  Definition answer (command : t) : Type :=
    match command with
    | Read => LString.t
    | Write => unit
    | FileRead => option LString.t
    | ServerSocketBind => option ServerSocketId.t
    | ServerSocketAccept => option ClientSocketId.t
    | ClientSocketRead => option LString.t
    | ClientSocketWrite => bool
    | ClientSocketClose => bool
    | Time => N
    end.
End Command.
