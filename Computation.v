(** The definition of a computation, used to represent concurrent programs. *)
Require Import Coq.NArith.NArith.
Require Import ListString.All.

(** Definition of a computation. *)
Module C.
  Inductive t : Type :=
  | Ret : t
  | Par : t -> t -> t
  | Send : forall {output : Type} (input : Type), output -> (input -> t) -> t.

  Module Notations.
    Notation "'let!' i ':' I ':=' o 'in' X" := (Send I o (fun i => X))
      (at level 200, i ident, I at level 100, o at level 100, X at level 200).

    Notation "'do!' o 'in' X" := (Send unit o (fun _ => X))
      (at level 200, o at level 100, X at level 200).
  End Notations.
End C.
