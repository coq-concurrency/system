Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.
Require Import Computation.
Require Import Pervasives.

Import ListNotations.
Open Local Scope type.

Module Heap.
  Inductive t (A : Type) : Type :=
  | Empty : t A
  | Node : A -> t A -> t A -> t A.
  Arguments Empty [A].
  Arguments Node [A] _ _ _.

  Fixpoint add (A : Type) (heap : t A) (x : A) (n : positive) : t A :=
    match (heap, n) with
    | (Empty, _) => Node x Empty Empty
    | (Node y heap1 heap2, xH) => Node y (add A heap1 x n) heap2
    | (Node y heap1 heap2, xO n) => Node y (add A heap1 x n) heap2
    | (Node y heap1 heap2, xI n) => Node y heap1 (add A heap2 x n)
    end.

  Fixpoint find (A : Type) (heap : t A) (n : positive) : option A :=
    match (heap, n) with
    | (Empty, _) => None
    | (Node x _ _, xH) => Some x
    | (Node x heap _, xO n) => find A heap n
    | (Node x _ heap, xI n) => find A heap n
    end.

  Module Tests.
    Definition h :=
      let h := add _ Empty 1 1 in
      let h := add _ h 2 2 in
      let h := add _ h 3 3 in
      let h := add _ h 4 4 in
      add _ h 5 5.

    Definition test1 : h = Node 1 (Node 2 (Node 4 Empty Empty) Empty)
      (Node 3 (Node 5 Empty Empty) Empty) :=
      eq_refl.

    Definition test2 : find _ Empty 3 = None (A := nat) :=
      eq_refl.

    Definition test3 : find _ h 3 = Some 3 :=
      eq_refl.
  End Tests.
End Heap.

Module CallBacks.
  Record t (sig : Signature.t) : Type := New {
    heap : Heap.t {command : Command.t & Command.answer command -> C.t sig unit};
    next : positive }.

  Definition empty (sig : Signature.t) : t sig := {|
    heap := Heap.Empty;
    next := xH |}.

  Definition add (sig : Signature.t) (call_backs : t sig) (command : Command.t)
    (call_back : Command.answer command -> C.t sig unit) : positive * t sig :=
    let id := next _ call_backs in
    (id, {|
      heap := Heap.add _ (heap _ call_backs) (existT _ command call_back) id;
      next := id + 1 |}).

  Definition find (sig : Signature.t) (call_backs : t sig) (command : Command.t)
    (id : positive) : option (Command.answer command -> C.t sig unit) :=
    match Heap.find _ (heap _ call_backs) id with
    | None => None
    | Some (existT command' call_back) =>
      match Command.eq_dec command command' with
      | left Heq =>
          eq_rect_r (fun c => option (Command.answer c -> C.t sig unit))
            (Some call_back) Heq
      | right _ => None
      end
    end.
End CallBacks.

Fixpoint run_aux (sig : Signature.t) (A : Type) (call_backs : CallBacks.t sig)
  (mem : Memory.t sig) (outputs : list Output.t) (x : C.t sig A)
  : option A * CallBacks.t sig * Memory.t sig * list Output.t :=
  match x with
  | C.Ret _ x => (Some x, call_backs, mem, outputs)
  | C.Bind _ _ x f =>
    match run_aux _ _ call_backs mem outputs x with
    | (Some x, call_backs, mem, outputs) =>
      run_aux _ _ call_backs mem outputs (f x)
    | (None, call_backs, mem, outputs) => (None, call_backs, mem, outputs)
    end
  | C.Read _ _ => (Some (Ref.read mem), call_backs, mem, outputs)
  | C.Write _ _ v => (Some tt, call_backs, Ref.write mem v, outputs)
  | C.Send command request call_back =>
    let (id, call_backs) := CallBacks.add _ call_backs command call_back in
    let output := Output.New command id request in
    (Some tt, call_backs, mem, output :: outputs)
  | C.Exit _ => (None, call_backs, mem, outputs)
  end.

(** Run a computation on an initialized shared memory. *)
Definition run (sig : Signature.t) (A : Type) (mem : Memory.t sig)
  (x : C.t sig A) : option A * CallBacks.t sig * Memory.t sig * list Output.t :=
  run_aux _ _ (CallBacks.empty _) mem [] x.
Arguments run [sig A] _ _.