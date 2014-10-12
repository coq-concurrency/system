(** A simple HTTP web server. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import LString.LString.
Require Import "Computation".
Require Import "Events".
Require Import "StdLib".

Import ListNotations.
Import C.Notations.
Local Open Scope type.
Local Open Scope string.
Local Open Scope char.
Local Open Scope list.

Definition apply {A B} (f : A -> B) (x : A) := f x.
Notation " x |> f " := (apply f x)
  (at level 40, left associativity).
Notation " f @@ x " := (apply f x)
  (at level 42, right associativity).

Module Option.
  Definition bind (A B : Type) (x : option A) (f : A -> option B) : option B :=
    match x with
    | Some x => f x
    | None => None
    end.
  Arguments bind [A B] _ _.
End Option.

Module Sum.
  Definition bind (E A B : Type) (x : A + E) (f : A -> B + E) : B + E :=
    match x with
    | inl x => f x
    | inr e => inr e
    end.
  Arguments bind [E A B] _ _.
End Sum.

(** The kind of HTTP method. *)
Module Method.
  (** For now, only the GET method is handled. *)
  Inductive t : Set :=
  | Get : t.

  Definition of_string (method : LString.t) : t + LString.t :=
    if LString.eqb method (LString.s "GET") then
      inl Get
    else
      inr (LString.s "unknown method " ++ method).
End Method.

Module Command.
  Definition t : Set := Method.t * LString.t * LString.t.

  Definition parse (command : LString.t) : t + LString.t :=
    match List.map LString.trim (LString.split (LString.trim command) " ") with
    | [method; arg1; arg2] =>
      Sum.bind (Method.of_string method) (fun method =>
      inl (method, arg1, arg2))
    | _ => inr @@ LString.s "three elements expected"
    end.
End Command.

Module Header.
  Module Kind.
    Inductive t : Set :=
    | Host : t.

    Definition of_string (kind : LString.t) : t + LString.t :=
      let kind := LString.down_case kind in
      if LString.eqb kind (LString.s "host") then
        inl Host
      else
        inr (LString.s "unknown header kind " ++ kind).
  End Kind.

  Record t : Set := New {
    kind : Kind.t;
    value : LString.t }.

  Definition parse (header : LString.t) : option t + LString.t :=
    match List.map LString.trim (LString.split_limit header ":" 2) with
    | [kind; value] =>
      match Kind.of_string kind with
      | inl kind => inl @@ Some @@ New kind value
      | inr _ => inl None
      end
    | _ => inr @@ LString.s "two elements expected"
    end.
End Header.

Module Request.
  Record t : Set := New {
    command : Command.t;
    headers : list Header.t;
    body : LString.t }.

  Fixpoint parse_aux (command : Command.t) (headers : list Header.t)
    (lines : list LString.t) : t + LString.t :=
    match lines with
    | [] => inr @@ LString.s "empty line expected"
    | line :: lines =>
      let line := LString.trim line in
      if LString.is_empty line then
        let body := List.fold_left (fun s1 s2 =>
          s1 ++ LString.Char.n :: s2)
          lines [] in
        inl @@ New command headers body
      else
        Sum.bind (Header.parse line) (fun header =>
        let headers :=
          match header with
          | None => headers
          | Some header => header :: headers
          end in
        parse_aux command headers lines)
    end.

  Definition parse (request : LString.t) : t + LString.t :=
    let lines := LString.split request LString.Char.n in
    match lines with
    | [] => inr @@ LString.s "the request is empty"
    | command :: lines =>
      Sum.bind (Command.parse command) (fun command =>
      parse_aux command [] lines)
    end.

  Definition test_parse : parse @@ LString.s "GET /page.html HTTP/1.0
Host: example.com
Referer: http://example.com/
User-Agent: CERN-LineMode/2.15 libwww/2.17b3

" = inl {|
      command := (Method.Get, LString.s "/page.html", LString.s "HTTP/1.0");
      headers := [Header.New Header.Kind.Host (LString.s "example.com")];
      body := [LString.Char.n] |} :=
    eq_refl.
End Request.

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

(** * Extraction. *)
Require Import Extraction.

Definition http_server := Extraction.run _ Memory.Nil program.
Extraction "tests/httpServer" http_server.