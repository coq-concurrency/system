(** The definition of a computation, used to represent concurrent programs. *)
Require Import Coq.Lists.List.
Require Import Events.

Import ListNotations.

(** A list of types to specify the shared memory. *)
Module Signature.
  Definition t := list Type.
End Signature.

(** The shared memory. *)
Module Memory.
  (** The shared memory is a list of typed cells. *)
  Inductive t : Signature.t -> Type :=
  | Nil : t []
  | Cons : forall (A : Type) (sig : Signature.t), A -> t sig -> t (A :: sig).
  Arguments Cons [A sig] _ _.
  
  (** The first shared memory cell. *)
  Definition head (A : Type) (sig : Signature.t) (mem : t (A :: sig)) : A :=
    match mem with
    | Cons _ _ x _ => x
    end.
  Arguments head [A sig] _.
  
  (** The tail of the shared memory. *)
  Definition tail (A : Type) (sig : Signature.t) (mem : t (A :: sig)) : t sig :=
    match mem with
    | Cons _ _ _ mem => mem
    end.
  Arguments tail [A sig] _.
End Memory.

(** A reference to a shared memory cell. *)
Module Ref.
  Class C (A : Type) (sig : Signature.t) : Type := New {
    read : Memory.t sig -> A;
    write : Memory.t sig -> A -> Memory.t sig }.

  Instance cons_left (A : Type) (sig : Signature.t) : C A (A :: sig) := {
    read mem := Memory.head mem;
    write mem x := Memory.Cons x (Memory.tail mem) }.

  Instance cons_right (A B : Type) (sig : Signature.t) (I : C A sig)
    : C A (B :: sig) := {
    read mem := read (Memory.tail mem);
    write mem x := Memory.Cons (Memory.head mem) (write (Memory.tail mem) x) }.
End Ref.

(** Definition of a computation. *)
Module C.
  Inductive t (sig : Signature.t) : Type -> Type :=
  | Ret : forall (A : Type), A -> t sig A
  | Bind : forall (A B : Type), t sig A -> (A -> t sig B) -> t sig B
  | Read : forall (A : Type), `{Ref.C A sig} -> t sig A
  | Write : forall (A : Type), `{Ref.C A sig} -> A -> t sig unit
  | Send : forall (command : Command.t), Command.request command ->
    (Command.answer command -> t sig unit) -> t sig unit
  | Exit : unit -> t sig unit.
  Arguments Ret [sig A] _.
  Arguments Bind [sig A B] _ _.
  Arguments Read [sig A] {_}.
  Arguments Write [sig A] {_} _.
  Arguments Send [sig] _ _ _.
  Arguments Exit [sig] _.

  (** Monadic notation. *)
  Module Notations.
    Notation "'let!' X ':=' A 'in' B" := (Bind A (fun X => B))
      (at level 200, X ident, A at level 100, B at level 200).

    Notation "'let!' X ':' T ':=' A 'in' B" := (Bind (A := T) A (fun X => B))
      (at level 200, X ident, A at level 100, T at level 200, B at level 200).

    Notation "'do!' A 'in' B" := (Bind A (fun _ => B))
      (at level 200, B at level 200).
  End Notations.
End C.

(** Functions on lists. *)
Module List.
  Import C.Notations.

  (** Iterate a computation over a list. *)
  Fixpoint iter (sig : Signature.t) (A : Type) (l : list A)
    (f : A -> C.t sig unit) : C.t sig unit :=
    match l with
    | [] => C.Ret tt
    | x :: l =>
      do! f x in
      iter _ _ l f
    end.
  Arguments iter [sig A] _ _.
End List.

(** Some basic tests. *)
(*Module Test.
  Require Import Coq.Strings.String.
  Import C.Notations.
  Open Local Scope string.

  Definition run (sig : Signature.t) (O A : Type)
    (mem : Memory.t sig) (x : C.t sig O A) : list O :=
    match C.run mem x with
    | (_, _, outputs) => outputs
    end.
  Arguments run [sig O A] _ _.

  Definition hello_world {sig : Signature.t} (_ : unit)
    : C.t sig (string + nat) unit :=
    do! C.Send (inl "Hello ") in
    C.Send (inl "world!").

  Check eq_refl : run Memory.Nil (hello_world tt) =
    [inl "world!"; inl "Hello "].

  Definition read_and_print {sig : Signature.t} `{Ref.C nat sig}
    (_ : unit) : C.t sig (string + nat) unit :=
    let! n : nat := C.Read _ in
    C.Send (inr n).

  Check eq_refl : run (Memory.Cons 12 Memory.Nil) (read_and_print tt) =
    [inr 12].

  Definition hello_read_print {sig : Signature.t} `{Ref.C nat sig}
    (_ : unit) : C.t sig (string + nat) unit :=
    do! hello_world tt in
    read_and_print tt.

  Check eq_refl : run (Memory.Cons 12 Memory.Nil) (hello_read_print tt) =
    [inr 12; inl "world!"; inl "Hello "].

  Definition incr_by {sig : Signature.t} `{Ref.C nat sig}
    (n : nat) : C.t sig nat unit :=
    let! m : nat := C.Read _ in
    C.Write _ (m + n).

  Definition double_print {sig : Signature.t} `{Ref.C nat sig}
    (n : nat) : C.t sig nat unit :=
    do! C.Write _ 0 in
    do! incr_by n in
    do! incr_by n in
    let! n : nat := C.Read _ in
    C.Send n.

  Check eq_refl : run (Memory.Cons 15 Memory.Nil) (double_print 12) = [24].
End Test.*)