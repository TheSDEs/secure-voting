use std::collections::HashMap;
use chrono::{DateTime, Utc};
use thiserror::Error;
use crate::crypto::{PublicKey, PrivateKey, KeyPair, CryptoError};
use num_bigint::BigInt;

#[derive(Error, Debug)]
pub enum VotingError {
    #[error("election not started")]
    NotStarted,
    #[error("election already started")]
    AlreadyStarted,
    #[error("election not ended")]
    NotEnded,
    #[error("election already ended")]
    AlreadyEnded,
    #[error("invalid vote")]
    InvalidVote,
    #[error("voter already voted")]
    AlreadyVoted,
    #[error("crypto error: {0}")]
    CryptoError(#[from] CryptoError),
}

#[derive(Clone, Debug)]
pub struct Ballot {
    voter_id: String,
    encrypted_vote: BigInt,
    timestamp: DateTime<Utc>,
}

#[derive(Debug)]
pub struct BallotBox {
    ballots: Vec<Ballot>,
    voters: HashMap<String, bool>,
}

#[derive(Debug)]
pub struct Election {
    title: String,
    description: String,
    options: Vec<String>,
    start_time: Option<DateTime<Utc>>,
    end_time: Option<DateTime<Utc>>,
    key_pair: KeyPair,
    ballot_box: BallotBox,
    status: ElectionStatus,
}

#[derive(Debug, PartialEq)]
pub enum ElectionStatus {
    Created,
    Started,
    Ended,
    ResultsPublished,
}

impl BallotBox {
    pub fn new() -> Self {
        BallotBox {
            ballots: Vec::new(),
            voters: HashMap::new(),
        }
    }

    pub fn add_ballot(&mut self, ballot: Ballot) -> Result<(), VotingError> {
        if self.voters.contains_key(&ballot.voter_id) {
            return Err(VotingError::AlreadyVoted);
        }
        self.voters.insert(ballot.voter_id.clone(), true);
        self.ballots.push(ballot);
        Ok(())
    }
}

impl Election {
    pub fn new(title: String, description: String, options: Vec<String>) -> Result<Self, Box<dyn std::error::Error>> {
        let key_pair = KeyPair::generate(2048)?;
        Ok(Election {
            title,
            description,
            options,
            start_time: None,
            end_time: None,
            key_pair,
            ballot_box: BallotBox::new(),
            status: ElectionStatus::Created,
        })
    }

    pub fn start(&mut self) -> Result<(), VotingError> {
        if self.status != ElectionStatus::Created {
            return Err(VotingError::AlreadyStarted);
        }
        self.start_time = Some(Utc::now());
        self.status = ElectionStatus::Started;
        Ok(())
    }

    pub fn end(&mut self) -> Result<(), VotingError> {
        if self.status != ElectionStatus::Started {
            return Err(VotingError::NotStarted);
        }
        self.end_time = Some(Utc::now());
        self.status = ElectionStatus::Ended;
        Ok(())
    }

    pub fn cast_vote(&mut self, voter_id: String, choice: usize) -> Result<(), VotingError> {
        if self.status != ElectionStatus::Started {
            return Err(VotingError::NotStarted);
        }
        if choice >= self.options.len() {
            return Err(VotingError::InvalidVote);
        }

        let vote = BigInt::from(choice as i32);
        let encrypted_vote = self.key_pair.public.encrypt(&vote)?;
        
        let ballot = Ballot {
            voter_id,
            encrypted_vote,
            timestamp: Utc::now(),
        };

        self.ballot_box.add_ballot(ballot)?;
        Ok(())
    }

    pub fn tally_votes(&mut self) -> Result<HashMap<String, u32>, VotingError> {
        if self.status != ElectionStatus::Ended {
            return Err(VotingError::NotEnded);
        }

        let mut results = HashMap::new();
        for option in &self.options {
            results.insert(option.clone(), 0);
        }

        for ballot in &self.ballot_box.ballots {
            let vote = self.key_pair.private.decrypt(&ballot.encrypted_vote)?;
            if let Some(choice) = vote.to_u32() {
                if choice < self.options.len() as u32 {
                    if let Some(count) = results.get_mut(&self.options[choice as usize]) {
                        *count += 1;
                    }
                }
            }
        }

        self.status = ElectionStatus::ResultsPublished;
        Ok(results)
    }
}
