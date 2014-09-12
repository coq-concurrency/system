(** Experiments for a file system API. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Computation.

Import ListNotations.
Import C.Notations.
Open Local Scope string.

(** The name of a file. *)
Module FileName.
  (** A file name is a path and a base name. *)
  Record t : Type := {
    path : list string;
    name : string }.

  (** Convert a file name to a single string. *)
  Definition to_string (file_name : t) : string :=
    name file_name.
End FileName.

(** A file identifier (used by the system). *)
Module FileId.
  (** For example, a natural number. *)
  Definition t : Type := nat.
End FileId.

(** Incoming events. *)
Module Input.
  Inductive t : Type :=
  | cannot_open : FileName.t -> t (** Cannot open a file. *)
  | opened : FileId.t -> t (** A file had be opened. *)
  | read : FileId.t -> option string -> t (** The file content had been read. *).
End Input.

(** Generated events. *)
Module Output.
  Inductive t : Type :=
  | log : string -> t (** Log a message on the standard output. *)
  | open : FileName.t -> t (** Open a file. *)
  | read : FileId.t -> t (** Read all the content of a file. *).
End Output.

(** Basic functions to interact with the system. *)
Module StdLib.
  (** Log a message on the standard output. *)
  Definition log {sig : Signature.t} (message : string)
    : C.t sig Output.t unit :=
    C.write (Output.log message).

  (** Open a file. *)
  Definition open {sig : Signature.t} (file_name : FileName.t)
    : C.t sig Output.t unit :=
    C.write (Output.open file_name).

  (** Read all the content of a file. *)
  Definition read {sig : Signature.t} (file : FileId.t)
    : C.t sig Output.t unit :=
    C.write (Output.read file).
End StdLib.

(** A test program which opens, reads and prints a file. *)
Module Test.
  (** The file to open. *)
  Definition resolv : FileName.t := {|
    FileName.path := ["etc"];
    FileName.name := "resolv.conf" |}.

  (** Start the program. *)
  Definition start {sig : Signature.t} (_ : unit) : C.t sig Output.t unit :=
    StdLib.open resolv.

  (** Handle events. *)
  Definition handler {sig : Signature.t} (input : Input.t)
    : C.t sig Output.t unit :=
    match input with
    | Input.cannot_open file_name =>
      StdLib.log ("cannot open the file " ++ (FileName.to_string file_name))
    | Input.opened file => StdLib.read file
    | Input.read _ None => StdLib.log "cannot read the file"
    | Input.read _ (Some data) => StdLib.log data
    end.

  (** Run the program sequentially on a list of input events. *)
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