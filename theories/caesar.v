Require Import Ascii.
Require Import String.
Require Import Program.
Require Import ZArith.
Require Import Bool.
Require Import Lia.
Require Import ssreflect.
Require Import ssrbool.
Require Import Zify.
Require Import List.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Local Obligation Tactic := try (solve [program_simpl]).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Create HintDb caesar_db.

Open Scope Z_scope.

Definition alphabet_size := 26.
Definition ascii_A := 65.
Definition thirteen := 13.

Open Scope char_scope.

Definition is_ascii_uppercase (c : ascii) : bool :=
  match c with
    | "A"
    | "B"
    | "C"
    | "D"
    | "E"
    | "F"
    | "G"
    | "H"
    | "I"
    | "J"
    | "K"
    | "L"
    | "M"
    | "N"
    | "O"
    | "P"
    | "Q"
    | "R"
    | "S"
    | "T"
    | "U"
    | "V"
    | "W"
    | "X"
    | "Y"
    | "Z" => true
    | _ => false
  end.

Close Scope char_scope.

Definition Z_of_ascii (c : ascii) := Z.of_nat (nat_of_ascii c).
Definition ascii_of_Z (n : Z) := ascii_of_nat (Z.to_nat n).

Definition is_uppercase_encoded (c : ascii) : Prop := 0 <= Z_of_ascii c < alphabet_size.

Definition text := { s : string | Forall is_uppercase_encoded (list_ascii_of_string s) }.

Definition encode (c : ascii) : ascii :=
  ascii_of_Z (Z_of_ascii c - ascii_A).

Definition decode (c : ascii) : ascii :=
  ascii_of_Z (Z_of_ascii c + ascii_A).

Definition shifted k c := { c' : ascii | Z_of_ascii c' = (Z_of_ascii c + k) mod alphabet_size }.

Hint Unfold alphabet_size ascii_A thirteen is_ascii_uppercase is_uppercase_encoded proj1_sig Z_of_ascii ascii_of_Z encode decode : caesar_db.

Program Definition shift (k : Z) (c : ascii) : shifted k c :=
  ascii_of_Z ((((Z_of_ascii c + k) mod alphabet_size) + alphabet_size) mod alphabet_size).
Next Obligation.
  autounfold with caesar_db; move => * //=; rewrite nat_ascii_embedding; lia.
Qed.

Program Definition text_of_string (s : string) : option text :=
  match String.forallb is_ascii_uppercase s with
    | true => Some (String.map encode s)
    | false => None
  end.
Next Obligation.
  elim => //=.
  move => c s' IHs'.
  move => /(@eq_sym bool) /andP [H1 H2].
  autounfold with caesar_db.
  destruct c; repeat match goal with [ b : bool |- _ ] => destruct b end; inversion H1; (constructor; [rewrite nat_ascii_embedding //=; lia |]); auto.
Qed.

Program Definition string_of_text (t : text) : { s : string | String.forallb is_ascii_uppercase s = true } := String.map decode t.
Next Obligation.
  move => [t H] //=; move: H.
  induction t as [| c s' IHs'] => //=.
  move => H; inversion H as [|? ? [H1 H2] ?]; subst.
  rewrite andb_true_iff; split; auto.
  destruct c; repeat match goal with [ b : bool |- _ ] => destruct b end; inversion H2; auto.
Qed.

Program Definition encrypted (ciphertext : text) (plaintext : text) (k : Z) : Prop :=
  Forall2 (fun c' c => c' = shift k c) (list_ascii_of_string ciphertext) (list_ascii_of_string plaintext).

Program Definition decrypted (plaintext : text) (ciphertext : text) (k : Z) : Prop :=
  encrypted plaintext ciphertext (-k).

Hint Unfold shift encrypted decrypted : caesar_db.

Program Definition encrypt (s : text) (k : Z) : { s' : text | encrypted s' s k } :=
  String.map (fun c => shift k c) s.
Next Obligation.
  move => [s H] k; autounfold with caesar_db.
  elim s.
  - constructor.
  - move => c s' IHs' //=.
    constructor; auto.
    autounfold with caesar_db; rewrite nat_ascii_embedding; lia.
Qed.
Next Obligation.
  move => [s H] k; autounfold with caesar_db.
  elim s.
  - constructor.
  - move => c s' IHs' //=.
    constructor; auto.
Qed.

Program Definition decrypt (s : text) (k : Z) : { s' : text | decrypted s' s k } :=
  encrypt s (-k).

Definition rot13 (s : text) : { s' | encrypted s' s thirteen } := encrypt s thirteen.

Lemma encrypt_id : forall (s : text), (` (` (encrypt s 0))) = (` s).
Proof.
  move => [s H] //=.
  induction s as [| c s IHs].
  - easy.
  - move => //=; f_equal; inversion H as [| ? ? [H1 H2]]; subst.
    + destruct c; repeat match goal with [ b : bool |- _ ] => destruct b end; inversion H2; auto.
    + now apply IHs.
Qed.

Lemma encrypt_mod : forall (s : text) (k : Z), (` (` (encrypt s k))) = (` (` (encrypt s (k mod alphabet_size)))).
Proof.
  move => [s H] k //=.
  induction s as [| c s IHs].
  - easy.
  - simpl; f_equal; inversion H; subst.
    + f_equal. now rewrite Zplus_mod_idemp_r.
    + now apply IHs.
Qed.

Lemma encrypt_trans : forall (s : text) (k l : Z),
    (` (` (encrypt (` (encrypt s k)) l))) = (` (` (encrypt s (k + l)))).
Proof.
  move => [s H] k l //=.
  induction s as [| c s IHs].
  - easy.
  - simpl; f_equal.
    + autounfold with caesar_db.
      rewrite nat_ascii_embedding; [| f_equal ]; lia.
    + inversion H; now apply IHs.
Qed.

Corollary rot13_involutive : forall (s : text), (` (` (rot13 (` (rot13 s))))) = (` s).
Proof.
  move => s.
  unfold rot13, thirteen; rewrite encrypt_trans.
  rewrite encrypt_mod. unfold alphabet_size.
  change ((13 + 13) mod 26) with 0.
  apply encrypt_id.
Qed.
