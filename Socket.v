Require Import Coq.NArith.NArith.

Module Client.
  (** The id of a client socket. *)
  Module Id.
    (** A socket id is a natural number. *)
    Inductive t : Set :=
    | New : N -> t.
  End Id.
End Client.

Module Server.
  (** The id of a server socket. *)
  Module Id.
    (** A socket id is a natural number. *)
    Inductive t : Set :=
    | New : N -> t.
  End Id.
End Server.
