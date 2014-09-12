(** The definition of a computation, used to represent concurrent programs. *)
Require Import Coq.Lists.List.

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
    get : Memory.t sig -> A;
    set : Memory.t sig -> A -> Memory.t sig }.

  Instance cons_left (A : Type) (sig : Signature.t) : C A (A :: sig) := {
    get mem := Memory.head mem;
    set mem x := Memory.Cons x (Memory.tail mem) }.

  Instance cons_right (A B : Type) (sig : Signature.t) (I : C A sig)
    : C A (B :: sig) := {
    get mem := get (Memory.tail mem);
    set mem x := Memory.Cons (Memory.head mem) (set (Memory.tail mem) x) }.
End Ref.

(** Definition of a computation. *)
Module C.
  Inductive t (sig : Signature.t) (O : Type) : Type -> Type :=
  | ret : forall (A : Type), A -> t sig O A
  | bind : forall (A B : Type), t sig O A -> (A -> t sig O B) -> t sig O B
  | get : forall (A : Type), `{Ref.C A sig} -> t sig O A
  | set : forall (A : Type), `{Ref.C A sig} -> A -> t sig O unit
  | write : O -> t sig O unit.
  Arguments ret [sig O A] _.
  Arguments bind [sig O A B] _ _.
  Arguments get [sig O A] {_}.
  Arguments set [sig O A] {_} _.
  Arguments write [sig O] _.

  Fixpoint run_aux (sig : Signature.t) (O A : Type)
    (mem : Memory.t sig) (output : list O) (x : t sig O A)
    : A * Memory.t sig * list O :=
    match x with
    | ret _ x => (x, mem, output)
    | bind _ _ x f =>
      match run_aux _ _ _ mem output x with
      | (x, mem, output) => run_aux _ _ _ mem output (f x)
      end
    | get _ _ => (Ref.get mem, mem, output)
    | set _ _ v => (tt, Ref.set mem v, output)
    | write v => (tt, mem, v :: output)
    end.

  (** Run a computation on an initialized shared memory. *)
  Definition run (sig : Signature.t) (O A : Type)
    (mem : Memory.t sig) (x : t sig O A)
    : A * Memory.t sig * list O :=
    run_aux _ _ _ mem [] x.
  Arguments run [sig O A] _ _.

  (** Monadic notation. *)
  Module Notations.
    Notation "'let!' X ':=' A 'in' B" := (bind A (fun X => B))
      (at level 200, X ident, A at level 100, B at level 200).

    Notation "'let!' X ':' T ':=' A 'in' B" := (bind (A := T) A (fun X => B))
      (at level 200, X ident, A at level 100, T at level 200, B at level 200).

    Notation "'do!' A 'in' B" := (bind A (fun _ => B))
      (at level 200, B at level 200).
  End Notations.
End C.

(** Functions on lists. *)
Module List.
  Import C.Notations.

  (** Iterate a computation over a list. *)
  Fixpoint iter (sig : Signature.t) (O A : Type)
    (l : list A) (f : A -> C.t sig O unit)
    : C.t sig O unit :=
    match l with
    | [] => C.ret tt
    | x :: l =>
      do! f x in
      iter _ _ _ l f
    end.
  Arguments iter [sig O A] _ _.
End List.

(** Some basic tests. *)
Module Test.
  Require Import Coq.Strings.String.
  Import C.Notations.
  Open Local Scope string.

  Definition hello_world {sig : Signature.t} (_ : unit)
    : C.t sig (string + nat) unit :=
    do! C.write (inl "Hello ") in
    C.write (inl "world!").

  Compute C.run Memory.Nil (hello_world tt).

  Definition read_and_print {sig : Signature.t} `{Ref.C nat sig}
    (_ : unit) : C.t sig (string + nat) unit :=
    let! n : nat := C.get _ in
    C.write (inr n).

  Compute C.run (Memory.Cons 12 Memory.Nil) (read_and_print tt).

  Definition hello_read_print {sig : Signature.t} `{Ref.C nat sig}
    (_ : unit) : C.t sig (string + nat) unit :=
    do! hello_world tt in
    read_and_print tt.

  Compute C.run (Memory.Cons 12 Memory.Nil) (hello_read_print tt).

  Definition incr_by {sig : Signature.t} `{Ref.C nat sig}
    (n : nat) : C.t sig nat unit :=
    let! m : nat := C.get _ in
    C.set _ (m + n).

  Definition double_print {sig : Signature.t} `{Ref.C nat sig}
    (n : nat) : C.t sig nat unit :=
    do! C.set _ 0 in
    do! incr_by n in
    do! incr_by n in
    let! n : nat := C.get _ in
    C.write n.

  Compute C.run (Memory.Cons 15 Memory.Nil) (double_print 12).
End Test.