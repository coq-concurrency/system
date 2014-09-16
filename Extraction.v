(** Extraction of computations to OCaml. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Computation.
Require Import Pervasives.
Require Import StdLib.

Import ListNotations.

(** * A nice extraction for strings. *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(** How to run output events. *)
Module Output.
  Module Log.
    Definition write (message : string) : unit := tt.
    Extract Constant write => "fun _ -> print_endline ""message""".
  End Log.

  Module File.
    Definition read (file_descriptors : unit) (file_name : string) : unit := tt.
    Extract Constant read => "fun file_descriptors file_name ->
  let file_name_string = List.fold_right (fun c s -> String.make 1 c ^ s) file_name """" in
  file_descriptors := (Unix.openfile file_name_string [Unix.O_RDONLY] 0o640, file_name) :: !file_descriptors".
  End File.

  Module TCPServerSocket.
    (* TODO *)
  End TCPServerSocket.

  Definition run (file_descriptors : unit) (output : Output.t) : unit :=
    match output with
    | Output.log output =>
      match output with
      | Log.Output.write message => Log.write message
      end
    | Output.file output =>
      match output with
      | File.Output.read file_name =>
        File.read file_descriptors (File.Name.to_string file_name)
      end
    | Output.socket _ => tt (* TODO *)
    end.
End Output.

Definition run_ocaml_aux (sig : Signature.t) (mem : Memory.t sig)
  (start : Memory.t sig -> Memory.t sig * list Output.t)
  (handler : Input.t -> Memory.t sig -> Memory.t sig * list Output.t)
  (run : unit -> Output.t -> unit)
  : unit := tt.
Extract Constant run_ocaml_aux => "fun _ mem start handler run ->
  let file_descriptors = ref [] in
  let (mem, outputs) = start mem in
  let mem = ref mem in
  let outputs = ref outputs in
  while true do
    List.iter (run file_descriptors) !outputs;
    let (reads, _, _) = Unix.select (List.map fst !file_descriptors) [] [] (-1.) in
    List.iter (fun read ->
      let file_name = List.assoc read !file_descriptors in
      match File.Name.of_string file_name with
      | None -> ()
      | Some file_name ->
        let input = Input.Coq_file (File.Input.Coq_read (file_name, ['c'; 'o'; 'n'; 't'; 'e'; 'n'; 't'])) in
        let (mem', outputs') = handler input !mem in
        mem := mem';
        outputs := outputs' @ !outputs)
      reads
  done".

Definition run_ocaml (sig : Signature.t) (mem : Memory.t sig)
  (start : unit -> C sig unit) (handler : Input.t -> C sig unit) : unit :=
  let last tuple :=
    match tuple with
    | (x, y, z) => (y, z)
    end in
  run_ocaml_aux sig mem (fun mem => last (C.run mem (start tt)))
    (fun input mem => last (C.run mem (handler input)))
    Output.run.