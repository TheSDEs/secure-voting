Require Import PaillierProof.

(* Test instances *)
Definition test_keypair := generate_keypair 2048.
Definition test_pk := get_public_key test_keypair.
Definition test_sk := get_private_key test_keypair.

(* Test encryption/decryption *)
Definition test_message := 42.
Definition test_encrypted := encrypt test_pk test_message.
Definition test_decrypted := decrypt test_sk test_encrypted.

(* Test homomorphic property *)
Definition test_message1 := 15.
Definition test_message2 := 27.
Definition test_encrypted1 := encrypt test_pk test_message1.
Definition test_encrypted2 := encrypt test_pk test_message2.
Definition test_sum := add_ciphertexts test_pk test_encrypted1 test_encrypted2.
Definition test_decrypted_sum := decrypt test_sk test_sum.

(* Verification theorems *)
Theorem test_correctness :
  test_decrypted = test_message.
Proof.
  unfold test_decrypted, test_encrypted, test_message.
  rewrite decrypt_encrypt.
  reflexivity.
Qed.

Theorem test_homomorphic :
  test_decrypted_sum = test_message1 + test_message2.
Proof.
  unfold test_decrypted_sum, test_sum, test_encrypted1, test_encrypted2.
  rewrite homomorphic_addition.
  reflexivity.
Qed.
