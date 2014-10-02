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
    | (Node y heap _, xH) => add A heap x n
    | (Node y heap _, xO n) => add A heap x n
    | (Node y _ heap, xI n) => add A heap x n
    end.

  Fixpoint find (A : Type) (heap : t A) (n : positive) : option A :=
    match (heap, n) with
    | (Empty, _) => None
    | (Node x _ _, xH) => Some x
    | (Node x heap _, xO n) => find A heap n
    | (Node x _ heap, xI n) => find A heap n
    end.
End Heap.

Module CallBacks.
  Record t (sig : Signature.t) : Type := New {
    heap : Heap.t {command : Command.t & Command.answer command -> C.t sig unit};
    next : positive }.

  Definition empty (sig : Signature.t) : t sig := {|
    heap := Heap.Empty;
    next := xH |}.

  Definition add (sig : Signature.t) (call_backs : t sig) (command : Command.t)
    (call_back : Command.answer command -> C.t sig unit) : t sig := {|
    heap := Heap.add _ (heap _ call_backs) (existT _ command call_back)
      (next _ call_backs);
    next := next _ call_backs + 1 |}.

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