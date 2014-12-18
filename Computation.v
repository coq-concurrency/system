(** The definition of a computation, used to represent concurrent programs. *)
Require Import Coq.NArith.NArith.
Require Import ListString.All.
Require Import Events.

(** Definition of a computation. *)
Module C.
  Inductive t : Type :=
  | Ret : t
  | Par : t -> t -> t
  | Send : forall (command : Command.t), Command.request command ->
    (Command.answer command -> t) -> t.

  Module Notations.
    Notation "'let!' A ':=' C '@' R 'in' X" := (Send C R (fun A => X))
      (at level 200, A ident, C at level 100, R at level 100, X at level 200).

    Notation "'do!' C '@' R 'in' X" := (Send C R (fun _ => X))
      (at level 200, C at level 100, R at level 100, X at level 200).
  End Notations.
End C.
