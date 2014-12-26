Require Import Coq.NArith.NArith.

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
