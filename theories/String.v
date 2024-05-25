Require Import Ascii List.
Require Export Coq.Strings.String.

Fixpoint map (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (map f s')
  end.

Fixpoint forallb (f : ascii -> bool) (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => f c && forallb f s'
  end.
