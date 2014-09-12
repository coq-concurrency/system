(** Experiments for a file system API. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Computation.

Import ListNotations.
Import C.Notations.
Open Local Scope string.

Module FileName.
  Record t : Type := {
    path : list string;
    name : string }.

  Definition to_string (file_name : t) : string :=
    name file_name.
End FileName.

Module FileId.
  Definition t : Type := nat.
End FileId.

Module Output.
  Inductive t : Type :=
  | log : string -> t
  | open : FileName.t -> t
  | read : FileId.t -> t.
End Output.

Module Input.
  Inductive t : Type :=
  | cannot_open : FileName.t -> t
  | opened : FileId.t -> t
  | read : FileId.t -> option string -> t.
End Input.

Module StdLib.
  Definition log {sig : Signature.t} (message : string)
    : C.t sig Output.t unit :=
    C.write (Output.log message).

  Definition open {sig : Signature.t} (file_name : FileName.t)
    : C.t sig Output.t unit :=
    C.write (Output.open file_name).

  Definition read {sig : Signature.t} (file : FileId.t)
    : C.t sig Output.t unit :=
    C.write (Output.read file).
End StdLib.

Module Test.
  Definition start {sig : Signature.t} (_ : unit) : C.t sig Output.t unit :=
    StdLib.open {| FileName.path := ["etc"]; FileName.name := "resolv.conf" |}.

  Definition handler {sig : Signature.t} (input : Input.t)
    : C.t sig Output.t unit :=
    match input with
    | Input.cannot_open file_name =>
      StdLib.log ("cannot open the file " ++ (FileName.to_string file_name))
    | Input.opened file => StdLib.read file
    | Input.read _ None => StdLib.log "cannot read the file"
    | Input.read _ (Some data) => StdLib.log data
    end.
End Test.