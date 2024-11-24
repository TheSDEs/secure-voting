Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(* Basic definitions *)
Record PublicKey := mk_public_key { n : positive; g : positive }.
Record PrivateKey := mk_private_key { lambda : positive; mu : positive; pub : PublicKey }.
Record KeyPair := mk_keypair { public : PublicKey; private : PrivateKey }.

(* Test values *)
Definition test_pk := mk_public_key 15 16.
Definition test_sk := mk_private_key 4 11 test_pk.
Definition test_kp := mk_keypair test_pk test_sk.

(* Voting system specific properties *)
Record Vote := mk_vote {
  voter_id : positive;
  choice : positive
}.

Definition BallotBox := list Vote.

(* Core properties *)
Definition no_double_voting (bb : BallotBox) : Prop :=
  forall v1 v2 : Vote,
    In v1 bb -> In v2 bb ->
    v1.(voter_id) = v2.(voter_id) ->
    v1 = v2.

Definition vote_integrity (bb : BallotBox) (pk : PublicKey) : Prop :=
  forall v : Vote,
    In v bb ->
    Pos.lt v.(choice) pk.(n).

(* Main theorems *)
Theorem no_double_votes_preserves_integrity :
  forall (bb : BallotBox) (pk : PublicKey),
    no_double_voting bb ->
    vote_integrity bb pk ->
    forall v : Vote,
      In v bb ->
      Pos.lt v.(choice) pk.(n).
Proof.
  intros bb pk H_no_double H_integrity v H_in.
  apply H_integrity.
  exact H_in.
Qed.

(* Tally properties *)
Definition valid_vote (v : Vote) (pk : PublicKey) : Prop :=
  Pos.lt v.(choice) pk.(n).

Definition valid_ballot_box (bb : BallotBox) (pk : PublicKey) : Prop :=
  forall v : Vote, In v bb -> valid_vote v pk.

Theorem valid_box_implies_valid_votes :
  forall (bb : BallotBox) (pk : PublicKey),
    valid_ballot_box bb pk ->
    forall v : Vote,
      In v bb ->
      valid_vote v pk.
Proof.
  intros bb pk H_valid v H_in.
  apply H_valid.
  exact H_in.
Qed.

(* Privacy properties *)
Definition vote_privacy (bb : BallotBox) : Prop :=
  forall v1 v2 : Vote,
    In v1 bb -> In v2 bb ->
    v1.(voter_id) <> v2.(voter_id).

Theorem privacy_no_double_voting :
  forall bb : BallotBox,
    vote_privacy bb ->
    no_double_voting bb.
Proof.
  intros bb H_privacy v1 v2 H_in1 H_in2 H_id.
  assert (v1.(voter_id) <> v2.(voter_id)).
  { apply H_privacy; assumption. }
  contradiction.
Qed.
