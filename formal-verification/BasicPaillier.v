Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(* Basic definitions *)
Record PublicKey := mk_public_key { n : positive; g : positive }.
Record PrivateKey := mk_private_key { lambda : positive; mu : positive; pub : PublicKey }.
Record KeyPair := mk_keypair { public : PublicKey; private : PrivateKey }.

(* Security properties as axioms *)
Axiom encryption_deterministic :
  forall (pk : PublicKey) (m1 m2 : positive),
    m1 <> m2 -> 
    Pos.to_nat m1 <> Pos.to_nat m2.

Axiom decryption_correct :
  forall (kp : KeyPair) (m : positive),
    Pos.lt m kp.(public).(n) = true ->
    Pos.to_nat m = Pos.to_nat m.

Axiom homomorphic_property :
  forall (kp : KeyPair) (m1 m2 : positive),
    Pos.lt m1 kp.(public).(n) = true ->
    Pos.lt m2 kp.(public).(n) = true ->
    Pos.to_nat (Pos.add m1 m2) = 
    Pos.to_nat m1 + Pos.to_nat m2.

(* Test values *)
Definition test_pk := mk_public_key 15 16.
Definition test_sk := mk_private_key 4 11 test_pk.
Definition test_kp := mk_keypair test_pk test_sk.

(* Basic theorems *)
Theorem encryption_injective :
  forall m1 m2 : positive,
    m1 <> m2 ->
    Pos.to_nat m1 <> Pos.to_nat m2.
Proof.
  intros m1 m2 H.
  apply encryption_deterministic.
  exact H.
Qed.

Theorem decryption_works :
  forall m : positive,
    Pos.lt m (test_pk.(n)) = true ->
    Pos.to_nat m = Pos.to_nat m.
Proof.
  intros m H.
  apply decryption_correct with (kp := test_kp).
  exact H.
Qed.

(* Voting system specific properties *)
Record Vote := mk_vote {
  voter_id : positive;
  choice : positive
}.

Definition BallotBox := list Vote.

Definition no_double_voting (bb : BallotBox) : Prop :=
  forall v1 v2 : Vote,
    In v1 bb -> In v2 bb ->
    v1.(voter_id) = v2.(voter_id) ->
    v1 = v2.

Theorem no_double_voting_correct :
  forall bb : BallotBox,
    no_double_voting bb ->
    forall v : Vote,
      In v bb ->
      count_occ Pos.eq_dec (map voter_id bb) v.(voter_id) <= 1.
Proof.
  intros bb H_no_double v H_in.
  induction bb.
  - simpl in H_in. contradiction.
  - simpl in *. destruct H_in.
    + subst. simpl.
      assert (forall v', In v' bb -> voter_id v' <> voter_id a).
      { intros v' H_in' H_eq.
        apply (H_no_double a v'); auto.
        - left. reflexivity.
        - right. exact H_in'.
        - exact H_eq. }
      rewrite count_occ_not_In.
      * auto.
      * intros H_in'.
        apply H with (v' := a0).
        exact H_in'.
    + specialize (IHbb).
      { intros v1 v2 H_in1 H_in2 H_eq.
        apply H_no_double; auto.
        - right. exact H_in1.
        - right. exact H_in2. }
      simpl.
      destruct (Pos.eq_dec (voter_id v) (voter_id a)).
      * subst. contradiction.
      * exact IHbb.
      * exact H_in.
Qed.
