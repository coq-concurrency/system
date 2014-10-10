(** A simple HTTP web server. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import LString.LString.
Require Import "Computation".
Require Import "Events".
Require Import "StdLib".

Import ListNotations.
Import C.Notations.
Open Local Scope string.
Open Local Scope list.

(** The kind of HTTP method. *)
Module Method.
  (** For now, only the GET method is handled. *)
  Inductive t : Set :=
  | Get : t.

  Definition of_string (method : LString.t) : option t :=
    if LString.eqb method (LString.s "GET") then
      Some Get
    else
      None.
End Method.

(** Parse an HTTP request. *)
Definition parse (request : LString.t) : option (Method.t * LString.t) :=
  let items := LString.split request " " in
  match items with
  | method :: url :: _ =>
    match Method.of_string method with
    | Some method => Some (method, url)
    | _ => None
    end
  | _ => None
  end.

Definition test_parse : parse (LString.s "GET /page.html HTTP/1.0
Host: example.com
Referer: http://example.com/
User-Agent: CERN-LineMode/2.15 libwww/2.17b3") =
  Some (Method.Get, LString.s "/page.html") :=
  eq_refl.

Definition http_answer_OK (content : LString.t) : LString.t :=
  LString.s "HTTP/1.0 200 Not Found
Content-Type: text/plain
Server: Coq

" ++ content.

Definition http_answer_error : LString.t :=
  LString.s "HTTP/1.0 404 OK
Content-Type: text/plain
Server: Coq

404".

Definition program (argv : list LString.t) : C.t [] unit :=
  match argv with
  | [_; website_dir] =>
    Log.write (LString.s "Coq server starting on " ++ website_dir ++
      LString.s ".") (fun _ =>
    ServerSocket.bind 80 (fun client =>
      match client with
      | None =>
        Log.write (LString.s "Server socket failed.") (fun _ => C.Exit tt)
      | Some client =>
        do! Log.write (LString.s "Client connected.") (fun _ => C.Ret tt) in
        ClientSocket.read client (fun request =>
        match option_map parse request with
        | None | Some None => C.Ret tt
        | Some (Some (Method.Get, url)) =>
          let file_name := website_dir ++ url in
          do! Log.write (LString.s "Reading file: '" ++ file_name ++
            LString.s "'") (fun _ => C.Ret tt) in
          File.read file_name (fun content =>
          let answer := match content with
            | None => http_answer_error
            | Some content => http_answer_OK content
            end in
          ClientSocket.write client answer (fun _ =>
          ClientSocket.close client (fun is_closed =>
            let message := 
              if is_closed then
                LString.s "Client closed."
              else
                LString.s "Client cannot be closed." in
              Log.write message (fun _ => C.Ret tt))))
        end)
      end))
  | _ =>
    Log.write (LString.s "Exactly one parameter expected: the website folder.") (fun _ =>
    C.Exit tt)
  end.

(** Extraction. *)
Require Import Extraction.

Definition http_server := Extraction.run _ Memory.Nil program.
Extraction "tests/httpServer" http_server.