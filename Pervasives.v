(** Basic type and event definitions. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import String.

Import ListNotations.
Open Local Scope string.

(** Events to log data. *)
Module Log.
  Module Output.
    Inductive t : Set :=
    | write (message : string).
  End Output.
End Log.

(** Events to read files. *)
Module File.
  (** The name of a file. Only relative for now. *)
  Module Name.
    (** A file name is a path and a base name. *)
    Record t : Set := {
      path : list string;
      base : string }.

    (** Convert a file name to a single string. *)
    Definition to_string (file_name : t) : string :=
      List.fold_right (fun x y => (x ++ "/" ++ y) % string) (base file_name)
        (path file_name).

    Check eq_refl : to_string {|
      path := ["some"; "dir"];
      base := "file.txt" |} =
      "some/dir/file.txt".

    (** Test equality. *)
    Definition eqb (file_name1 file_name2 : t) : bool :=
      if List.list_eq_dec string_dec (path file_name1) (path file_name2) then
        String.eqb (base file_name1) (base file_name2)
      else
        false.

    (** Parse a string into a file name. *)
    Definition of_string (file_name : string) : option t :=
      let names : list string := String.split file_name "/" in
      match List.rev names with
      | base :: path => Some {|
        File.Name.path := List.rev path;
        File.Name.base := base |}
      | [] => None
      end.
  End Name.

  (** Incoming events. *)
  Module Input.
    Inductive t : Set :=
    | read ( file_name : Name.t) (content : string)
      (** All the file content had been read. *).
  End Input.

  (** Generated events. *)
  Module Output.
    Inductive t : Set :=
    | read (file_name : Name.t) (** Read all the content of a file. *).
  End Output.
End File.

Module TCPClientSocket.
  Module Id.
    Require Import Coq.Numbers.Natural.Peano.NPeano.

    Inductive t : Set :=
    | new : nat -> t.

    (** Test equality. *)
    Definition eqb (id1 id2 : t) : bool :=
      match (id1, id2) with
      | (new id1, new id2) => Nat.eqb id1 id2
      end.
  End Id.

  Module Input.
    Inductive t : Set :=
    | accepted (id : Id.t)
    | read (id : Id.t) (content : string).
  End Input.

  Module Output.
    Inductive t : Set :=
    | write (id : Id.t) (message : string)
    | close (id : Id.t).
  End Output.
End TCPClientSocket.

Module TCPServerSocket.
  Module Id.
    Inductive t : Set :=
    | new : nat -> t.
  End Id.

  Module Input.
    Inductive t : Set :=
    | bound (id : Id.t).
  End Input.

  Module Output.
    Inductive t : Set :=
    | bind (port : nat)
    | close (id : Id.t).
  End Output.
End TCPServerSocket.

Module Input.
  Inductive t : Set :=
  | file : File.Input.t -> t
  | client_socket : TCPClientSocket.Input.t -> t
  | server_socket : TCPServerSocket.Input.t -> t.
End Input.

Module Output.
  Inductive t : Set :=
  | log : Log.Output.t -> t
  | file : File.Output.t -> t
  | client_socket : TCPClientSocket.Output.t -> t
  | server_socket : TCPServerSocket.Output.t -> t.
End Output.