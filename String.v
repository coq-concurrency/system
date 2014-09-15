(** Some helper functions to manipulate strings. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Import ListNotations.
Open Local Scope string.

(** Boolean equality test. *)
Fixpoint eqb (s1 s2 : string) : bool :=
  match (s1, s2) with
  | (EmptyString, EmptyString) => true
  | (EmptyString, String _ _) => false
  | (String _ _, EmptyString) => false
  | (String c1 s1, String c2 s2) =>
    if ascii_dec c1 c2 then
      eqb s1 s2
    else
      false
  end.

Check eq_refl : eqb "hi" "hi" = true.
Check eq_refl : eqb "hi" "bye" = false.

Fixpoint reverse_aux (s : string) (rev : string) : string :=
  match s with
  | EmptyString => rev
  | String c s => reverse_aux s (String c rev)
  end.

(** Reverse a string. *)
Definition reverse (s : string) : string :=
  reverse_aux s "".

Check eq_refl : reverse "hello" = "olleh".

Fixpoint split_aux (s : string) (c : ascii) (beginning : string)
  : list string :=
  match s with
  | EmptyString => [reverse beginning]
  | String c' s =>
    if ascii_dec c c' then
      reverse beginning :: split_aux s c ""
    else
      split_aux s c (String c' beginning)
  end.

(** Split a string at each occurrence of a given character. *)
Definition split (s : string) (c : ascii) : list string :=
  split_aux s c "".

Check eq_refl : split "go stop go" " " = ["go"; "stop"; "go"].
Check eq_refl : split "grr" " " = ["grr"].