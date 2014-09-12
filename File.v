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
  Definition resolv : FileName.t := {|
    FileName.path := ["etc"];
    FileName.name := "resolv.conf" |}.

  Definition start {sig : Signature.t} (_ : unit) : C.t sig Output.t unit :=
    StdLib.open resolv.

  Definition handler {sig : Signature.t} (input : Input.t)
    : C.t sig Output.t unit :=
    match input with
    | Input.cannot_open file_name =>
      StdLib.log ("cannot open the file " ++ (FileName.to_string file_name))
    | Input.opened file => StdLib.read file
    | Input.read _ None => StdLib.log "cannot read the file"
    | Input.read _ (Some data) => StdLib.log data
    end.

  Definition run (inputs : list Input.t) : list Output.t :=
    let program :=
      do! start tt in
      List.iter inputs handler in
    match C.run Memory.Nil program with
    | (_, _, output) => output
    end.

  Compute run [].
  Compute run [Input.cannot_open resolv].
  Compute run [Input.opened 12].
  Compute run [Input.opened 12; Input.read 12 None].
  Compute run [Input.opened 12; Input.read 12 (Some "nameserver 34.123.45.46")].
End Test.