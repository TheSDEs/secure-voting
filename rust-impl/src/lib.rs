pub mod crypto;
pub mod voting;

#[cfg(test)]
mod tests {
    use super::*;
    use chrono::{Duration, Utc};
    use assert_matches::assert_matches;
    use num_bigint::{BigUint, BigInt};
    use num_traits::{Zero, One};
    use crate::crypto::{KeyPair, PublicKey, PrivateKey};

    #[test]
    fn test_election_lifecycle() -> Result<(), Box<dyn std::error::Error>> {
        // Create a new election
        let options = vec![
            "Option A".to_string(),
            "Option B".to_string(),
            "Option C".to_string(),
        ];
        let start_time = Utc::now() - Duration::hours(1); // Start time 1 hour ago
        let end_time = start_time + Duration::minutes(30); // End time 30 minutes ago

        let mut election = voting::Election::new(
            "Test Election".to_string(),
            "Test Description".to_string(),
            options,
            start_time,
            end_time,
        )?;

        // Start the election
        election.start()?;
        assert_matches!(election.status, voting::ElectionStatus::Active);

        // Cast some votes
        let voters = vec!["voter1", "voter2", "voter3"];
        let choices = vec![0, 1, 2];

        for (voter, &choice) in voters.iter().zip(choices.iter()) {
            let ballot = election.cast(voter, choice)?;
            let receipt = ballot.get_receipt();
            assert!(!receipt.is_empty());
        }

        // Try to vote twice with the same ID
        assert!(election.cast("voter1", 0).is_err());

        // End the election
        election.end()?;
        assert_matches!(election.status, voting::ElectionStatus::Ended);

        // Tally votes
        let results = election.tally_votes()?;
        assert_matches!(election.status, voting::ElectionStatus::ResultsPublished);

        // Verify each option got exactly one vote
        for count in results.values() {
            assert_eq!(*count, 1);
        }

        Ok(())
    }

    #[test]
    fn test_crypto_operations() -> Result<(), Box<dyn std::error::Error>> {
        use num_bigint::BigInt;
        
        // Generate a key pair
        let key_pair = crypto::KeyPair::generate(2048)?;

        // Test encryption and decryption
        let message = BigInt::from(42);
        let encrypted = key_pair.public.encrypt(&message)?;
        let decrypted = key_pair.private.decrypt(&encrypted)?;
        assert_eq!(message, decrypted);

        // Test homomorphic addition
        let m1 = BigInt::from(30);
        let m2 = BigInt::from(12);
        
        let c1 = key_pair.public.encrypt(&m1)?;
        let c2 = key_pair.public.encrypt(&m2)?;
        
        let c_sum = key_pair.public.add(&c1, &c2);
        let m_sum = key_pair.private.decrypt(&c_sum)?;
        
        assert_eq!(m_sum, m1 + m2);

        Ok(())
    }

    #[test]
    fn test_key_generation() {
        let p = BigUint::parse_bytes(b"13", 10).unwrap();
        let q = BigUint::parse_bytes(b"17", 10).unwrap();
        let private_key = PrivateKey::new(p, q).unwrap();
        
        assert!(!private_key.public.n.is_zero());
        assert_eq!(private_key.public.n, BigUint::parse_bytes(b"221", 10).unwrap());
    }

    #[test]
    fn test_encryption_decryption() {
        let p = BigUint::parse_bytes(b"13", 10).unwrap();
        let q = BigUint::parse_bytes(b"17", 10).unwrap();
        let private_key = PrivateKey::new(p, q).unwrap();
        let public_key = &private_key.public;

        let message = BigInt::from(42i32);
        let encrypted = public_key.encrypt(&message).unwrap();
        let decrypted = private_key.decrypt(&encrypted).unwrap();

        assert_eq!(message, decrypted);
    }

    #[test]
    fn test_homomorphic_addition() {
        let p = BigUint::parse_bytes(b"13", 10).unwrap();
        let q = BigUint::parse_bytes(b"17", 10).unwrap();
        let private_key = PrivateKey::new(p, q).unwrap();
        let public_key = &private_key.public;

        let m1 = BigInt::from(30i32);
        let m2 = BigInt::from(12i32);
        let c1 = public_key.encrypt(&m1).unwrap();
        let c2 = public_key.encrypt(&m2).unwrap();

        let c_sum = public_key.add(&c1, &c2);
        let decrypted_sum = private_key.decrypt(&c_sum).unwrap();

        assert_eq!(decrypted_sum, m1 + m2);
    }
}
