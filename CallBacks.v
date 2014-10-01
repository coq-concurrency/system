Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import Computation.
Require Import Pervasives.

Import ListNotations.
Open Local Scope type.

Definition t (sig : Signature.t) : Type :=
  list {command : Command.t & N * (Command.answer command -> C sig unit)}.

Definition empty (sig : Signature.t) : t sig :=
  [].

Fixpoint add (sig : Signature.t) (call_backs : t sig) (command : Command.t)
  (id : N) (call_back : Command.answer command -> C sig unit) : t sig :=
  match call_backs with
  | [] => [existT _ command (id, call_back)]
  | existT command' (id', call_back') :: call_backs =>
    if andb (Command.eqb command command') (N.eqb id id') then
      existT _ command (id, call_back) :: call_backs
    else
      existT _ command' (id', call_back') ::
        add sig call_backs command id call_back
  end.

Fixpoint find (sig : Signature.t) (call_backs : t sig) (command : Command.t)
  (id : N) : option (Command.answer command -> C sig unit) :=
  match call_backs with
  | [] => None
  | existT command' (id', call_back') :: call_backs =>
    match Command.eq_dec command command' with
    | left Heq =>
      if N.eqb id id' then
        eq_rect_r (fun command => option (Command.answer command -> C sig unit))
          (Some call_back') Heq
      else
        find sig call_backs command id
    | right _ => find sig call_backs command id
    end
  end.

Fixpoint remove (sig : Signature.t) (call_backs : t sig) (command : Command.t)
  (id : N) : t sig :=
  match call_backs with
  | [] => []
  | existT command' (id', call_back') :: call_backs =>
    if andb (Command.eqb command command') (N.eqb id id') then
      call_backs
    else
      remove sig call_backs command id
  end.