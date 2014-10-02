(** A simple HTTP web server. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Computation.
Require Import Events.
Require Import StdLib.
Require Import String.

Import ListNotations.
Import C.Notations.
Open Local Scope string.

(** The kind of HTTP method. *)
Module Method.
  (** For now, only the GET method is handled. *)
  Inductive t : Set :=
  | Get : t.

  Definition of_string (method : string) : option t :=
    if String.eqb method "GET" then
      Some Get
    else
      None.
End Method.

(** Parse an HTTP request. *)
Definition parse (request : string) : option (Method.t * string) :=
  let items := String.split request " " in
  match items with
  | method :: url :: _ =>
    match Method.of_string method with
    | Some method => Some (method, url)
    | _ => None
    end
  | _ => None
  end.

Definition test_parse : parse "GET /page.html HTTP/1.0
Host: example.com
Referer: http://example.com/
User-Agent: CERN-LineMode/2.15 libwww/2.17b3" =
  Some (Method.Get, "/page.html") :=
  eq_refl.

Definition http_answer_OK (content : string) : string :=
  "HTTP/1.0 200 Not Found
Content-Type: text/plain
Server: Coq

" ++ content.

Definition http_answer_error : string :=
  "HTTP/1.0 404 OK
Content-Type: text/plain
Server: Coq

404".

Definition program : C.t [] unit :=
  Log.write "Coq server:" (fun _ =>
  ServerSocket.bind 80 (fun client =>
    match client with
    | None => Log.write "Server socket failed." (fun _ => C.Exit tt)
    | Some client =>
      do! Log.write "Client connected." (fun _ => C.Ret tt) in
      ClientSocket.read client (fun request =>
      match option_map parse request with
      | None | Some None => C.Ret tt
      | Some (Some (Method.Get, url)) =>
        do! Log.write ("Reading file: '" ++ url ++ "'") (fun _ => C.Ret tt) in
        File.read url (fun content =>
        let answer := match content with
          | None => http_answer_error
          | Some content => http_answer_OK content
          end in
        ClientSocket.write client answer (fun _ =>
        ClientSocket.close client (fun is_closed =>
          let message := 
            if is_closed then
              "Client closed."
            else
              "Client cannot be closed." in
            Log.write message (fun _ => C.Ret tt))))
      end)
    end)).

(** Extraction. *)
Require Import Extraction.

Definition http_server := Extraction.run _ Memory.Nil program.
Extraction "tests/httpServer" http_server.