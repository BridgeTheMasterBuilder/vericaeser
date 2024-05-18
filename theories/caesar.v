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

Definition string_is_uppercase_encoded (s : string) := Forall is_uppercase_encoded (list_ascii_of_string s).

Definition text := { s : string | string_is_uppercase_encoded s }.

Open Scope string_scope.

Definition text_ind : forall P : text -> Prop,
       (forall (H : string_is_uppercase_encoded ""), P (exist _ "" H)) ->
       (forall (c : ascii)
          (s : string)
          (H1 : string_is_uppercase_encoded s)
          (H2 : string_is_uppercase_encoded (String c s)),
           P (exist _ s H1) -> P (exist _ (String c s) H2)) ->
       forall t : text, P t.
  move => P base step.
  case; elim => //=; unfold string_is_uppercase_encoded.
  by move => c ? ? H; inversion H as [|? ? ? H']; apply (step _ _ H' _).
Qed.

Definition encode (c : ascii) : ascii :=
  ascii_of_Z (Z_of_ascii c - ascii_A).

Definition decode (c : ascii) : ascii :=
  ascii_of_Z (Z_of_ascii c + ascii_A).

Lemma encode_correct : forall (c : ascii), is_ascii_uppercase c -> is_uppercase_encoded (encode c).
Proof.
  move => [[] [] [] [] [] [] [] []]; easy.
Qed.

Lemma decode_correct : forall (c : ascii), is_uppercase_encoded c -> is_ascii_uppercase (decode c).
Proof.
  move => [[] [] [] [] [] [] [] []] []; easy.
Qed.

Definition shifted k c := { c' : ascii | Z_of_ascii c' = (Z_of_ascii c + k) mod alphabet_size }.

Hint Unfold alphabet_size ascii_A thirteen is_ascii_uppercase is_uppercase_encoded proj1_sig Z_of_ascii ascii_of_Z encode decode string_is_uppercase_encoded : caesar_db.

Program Definition shift (k : Z) (c : ascii) : shifted k c :=
  ascii_of_Z ((((Z_of_ascii c + k) mod alphabet_size) + alphabet_size) mod alphabet_size).
Next Obligation.
  autounfold with caesar_db; move => *; rewrite nat_ascii_embedding; lia.
Qed.

Program Definition text_of_string (s : string) : option text :=
  match String.forallb is_ascii_uppercase s with
    | true => Some (String.map encode s)
    | false => None
  end.
Next Obligation.
  unfold string_is_uppercase_encoded.
  elim => //=.
  move => ? ? IHs' /(@eq_sym bool) /andP [? ?].
  by constructor; [apply encode_correct | by auto].
Qed.

Program Definition string_of_text (t : text) : { s : string | String.forallb is_ascii_uppercase s = true } := String.map decode t.
Next Obligation.
  elim/text_ind => //=.
  unfold string_is_uppercase_encoded.
  move => ? ? ? /Forall_cons_iff [? ?] ?.
  by apply/andP; split; [apply decode_correct |].
Qed.

Program Definition encrypted (ciphertext : text) (plaintext : text) (k : Z) : Prop :=
  Forall2 (fun c' c => c' = shift k c) (list_ascii_of_string ciphertext) (list_ascii_of_string plaintext).

Program Definition decrypted (plaintext : text) (ciphertext : text) (k : Z) : Prop :=
  encrypted plaintext ciphertext (-k).

Hint Unfold shift encrypted decrypted : caesar_db.

Program Definition encrypt (s : text) (k : Z) : { s' : text | encrypted s' s k } :=
  String.map (fun c => shift k c) s.
Next Obligation.
  elim/text_ind => //=.
  unfold string_is_uppercase_encoded.
  move => ? ? ? /Forall_cons_iff [? ?] ? ?.
  constructor => //=; autounfold with caesar_db; rewrite nat_ascii_embedding; lia.
Qed.
Next Obligation.
  autounfold with caesar_db;
  elim/text_ind; first by constructor.
  by constructor.
Qed.

Program Definition decrypt (s : text) (k : Z) : { s' : text | decrypted s' s k } :=
  encrypt s (-k).

Definition rot13 (s : text) : { s' | encrypted s' s thirteen } := encrypt s thirteen.

Lemma encrypt_id : forall (s : text), (` (` (encrypt s 0))) = (` s).
Proof.
  elim/text_ind => //=.
  autounfold with caesar_db.
  move => c ? ? /Forall_cons_iff [[? ?] ?] ?; f_equal => //=.
  suff {2} <- : ascii_of_nat (Z.to_nat (Z.of_nat (nat_of_ascii c))) = c by f_equal; lia.
  by rewrite Nat2Z.id ascii_nat_embedding.
Qed.

Lemma encrypt_mod : forall (s : text) (k : Z), (` (` (encrypt s k))) = (` (` (encrypt s (k mod alphabet_size)))).
Proof.
  elim/text_ind => //=.
  autounfold with caesar_db.
  move => c ? ? /Forall_cons_iff [[? ?] ?] ? ?; f_equal => //=.
  by rewrite Zplus_mod_idemp_r.
Qed.

Lemma encrypt_trans : forall (s : text) (k l : Z),
    (` (` (encrypt (` (encrypt s k)) l))) = (` (` (encrypt s (k + l)))).
Proof.
  elim/text_ind => //=.
  autounfold with caesar_db.
  move => ? ? ? /Forall_cons_iff [[? ?] ?] ? ? ?; f_equal => //=.
  rewrite nat_ascii_embedding; [| f_equal ]; lia.
Qed.

Corollary rot13_involutive : forall (s : text), (` (` (rot13 (` (rot13 s))))) = (` s).
Proof.
  move => s.
  unfold rot13, thirteen; rewrite encrypt_trans.
  rewrite encrypt_mod. unfold alphabet_size.
  change ((13 + 13) mod 26) with 0.
  apply encrypt_id.
Qed.
