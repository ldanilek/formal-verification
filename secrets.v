
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.omega.Omega.

Fixpoint conv_to_string (n: nat) : string :=
  match n with
  | O => EmptyString
  | S m => String zero (conv_to_string m)
  end.

Lemma conv_to_string_inj: forall n m,
  conv_to_string n = conv_to_string m -> n = m.
Proof.
induction n, m; simpl; intros.
auto.
discriminate.
discriminate.
injection H; intro.
apply IHn in H0.
subst n. auto.
Qed.


Definition secrets_map : Type := string -> option string.
Definition uuid_state : Type := nat.
Record secrets_type : Type := mk_secret {
  secret_values: secrets_map;
  state: uuid_state;
  secrets_keys: list string;
  occupied_keys: forall key v, secret_values key = Some v -> In key secrets_keys;
  occupied_uuid: forall key, In key secrets_keys ->
    exists n, n < state /\ key = conv_to_string n;
}.



Definition available_key (secrets: secrets_type) : string :=
  conv_to_string (state secrets).

Lemma availability: forall secrets,
  ~ In (available_key secrets) (secrets_keys secrets).
Proof.
intros. intro.
apply (occupied_uuid secrets) in H.
destruct H as (n & n_le & conv).
unfold available_key in conv.
apply conv_to_string_inj in conv.
subst n.
omega.
Qed.

Definition with_new_secret
    (m: secrets_map) (k: string) (v: option string) (k': string) : option string :=
  match (k =? k')%string with
  | true => v
  | false => m k'
  end.

Lemma occupied_keys_with_new_secret:
    forall (secrets: secrets_type) (k: string) (v': string),
    forall key v,
    (with_new_secret (secret_values secrets) k (Some v')) key
      = Some v -> In key (k :: (secrets_keys secrets)).
Proof.
unfold with_new_secret.
intros.
remember ((k =? key)%string) as is_eq.
destruct is_eq.
-
symmetry in Heqis_eq.
apply String.eqb_eq in Heqis_eq. subst key.
simpl. left. auto.
-
simpl. right.
eapply (occupied_keys secrets). eauto.
Qed.

Lemma occupied_keys_with_deleted_secret:
    forall (secrets: secrets_type) (k: string),
    forall key v,
    (with_new_secret (secret_values secrets) k None) key
      = Some v -> In key (secrets_keys secrets).
Proof.
unfold with_new_secret.
intros.
remember ((k =? key)%string) as is_eq.
destruct is_eq.
- discriminate.
-
eapply (occupied_keys secrets).
eauto.
Qed.

Lemma occupied_with_new_secret:
    forall (secrets: secrets_type),
    forall key, In key ((available_key secrets) :: (secrets_keys secrets)) ->
      exists n, n < S (state secrets) /\ key = conv_to_string n.
Proof.
intros.
simpl in H. destruct H.
-
subst key. unfold available_key.
exists (state secrets).
split. omega. auto.
-
apply (occupied_uuid secrets) in H. destruct H as (n & n_le & conv).
exists n. split. omega. auto.
Qed.
(*
Lemma occupied_with_deleted_secret:
    forall (secrets: secrets_type),
    forall key, In key (secrets_keys secrets) ->
      exists n, n < state secrets /\ key = conv_to_string n.
Proof.
intros.
simpl in H. destruct H.
-
subst key. unfold available_key.
exists (state secrets).
split. omega. auto.
-
apply (occupied_uuid secrets) in H. destruct H as (n & n_le & conv).
exists n. split. omega. auto.
Qed.
*)

Definition store_secret (secrets: secrets_type) (secret: string)
    : prod string secrets_type :=
  let key := available_key secrets in
  (key,
  mk_secret
    (with_new_secret (secret_values secrets) key (Some secret))
    (S (state secrets))
    (key :: secrets_keys secrets)
    (occupied_keys_with_new_secret secrets key secret)
    (occupied_with_new_secret secrets)
  )
  .

Definition retrieve_secret (secrets: secrets_type) (key: string)
    : prod (option string) secrets_type :=
  (
  (secret_values secrets) key,
  mk_secret
    (with_new_secret (secret_values secrets) key None)
    (state secrets)
    (secrets_keys secrets)
    (occupied_keys_with_deleted_secret secrets key)
    (occupied_uuid secrets)
  ).

Lemma empty_keys: forall key v, (fun (x: string) => (None: option string)) key = Some v -> In key nil.
Proof.
simpl.
intros. discriminate.
Qed.

Lemma empty_uuid: forall key, In key nil ->
    exists n, n < O /\ key = conv_to_string n.
Proof.
simpl. intros. contradiction.
Qed.

Definition empty_secrets_type :=
  mk_secret
    (fun x => None)
    O
    nil
    empty_keys
    empty_uuid.


Theorem store_retrieve: forall secrets secret,
  let (key, secrets') := store_secret secrets secret in
  fst (retrieve_secret secrets' key) = Some secret.
Proof.
intros. remember (store_secret secrets secret) as xx. destruct xx as (key & secrets').
unfold retrieve_secret. simpl.
unfold store_secret in Heqxx. injection Heqxx; intros.
clear Heqxx.
subst. simpl.
unfold with_new_secret.
rewrite String.eqb_refl. trivial.
Qed.

Theorem add_before_retrieve: forall secrets secret secret' key,
  fst (retrieve_secret secrets key) = Some secret ->
  fst (retrieve_secret (snd (store_secret secrets secret')) key) = Some secret.
Proof.
simpl.
intros.
unfold with_new_secret.
assert ((available_key secrets =? key)%string = false).
apply (occupied_keys secrets) in H.
apply (occupied_uuid secrets) in H.
unfold available_key.
destruct H.
destruct H.
subst key.
apply String.eqb_neq.
intro.
apply conv_to_string_inj in H0.
omega.
rewrite H0.
apply H.
Qed.

Theorem retrieve_before_retrieve: forall secrets secret key' key,
  fst (retrieve_secret secrets key) = secret -> 
    fst (retrieve_secret (snd (retrieve_secret secrets key')) key) =
      if (key' =? key)%string then None else secret.
Proof.
simpl.
intros.
unfold with_new_secret.
rewrite H.
auto.
Qed.

Theorem add_before_retrieve_none: forall secrets secret key,
  fst (retrieve_secret secrets key) = None ->
  let (key', secrets') := store_secret secrets secret in
  fst (retrieve_secret secrets' key) =
  if (key' =? key)%string
  then Some secret
  else None.
Proof.
simpl. intros.
unfold with_new_secret. rewrite H. auto.
Qed.
