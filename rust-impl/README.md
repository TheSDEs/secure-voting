# Secure Voting System (Rust Implementation)

This is a secure, verifiable voting system implementation using homomorphic encryption. The system ensures voter privacy and verifiability while allowing votes to be tallied without decrypting individual ballots.

## Features

- Homomorphic encryption using the Paillier cryptosystem
- Secure ballot creation and verification
- Anonymous voting with voter receipts
- Homomorphic vote tallying
- Election lifecycle management
- Vote verification without compromising privacy

## Architecture

The system consists of several key components:

1. **Cryptographic Layer** (`src/crypto/mod.rs`)
   - Implementation of the Paillier cryptosystem
   - Key generation, encryption, and decryption
   - Homomorphic addition of encrypted votes
   - Miller-Rabin primality testing

2. **Voting System** (`src/voting/mod.rs`)
   - Ballot creation and verification
   - Election management and vote tallying
   - Secure voter ID hashing
   - Receipt generation

## Security Features

- Homomorphic encryption ensures votes remain encrypted during tallying
- Voter anonymity through SHA-256 hashed voter IDs
- Verifiable voting receipts
- Prevention of double voting
- Secure key generation and management
- Strong type system preventing common programming errors

## Getting Started

### Prerequisites

- Rust 1.70 or later
- Cargo package manager

### Dependencies

The project uses the following main dependencies:
- `num-bigint`: For arbitrary-precision arithmetic
- `rand`: For secure random number generation
- `sha2`: For cryptographic hashing
- `chrono`: For time management
- `thiserror`: For error handling

### Installation

1. Clone the repository
2. Build the project:
   ```bash
   cargo build --release
   ```

### Running Tests

```bash
cargo test
```

## Usage Example

```rust
use chrono::{Duration, Utc};
use secure_voting::voting::Election;

// Create a new election
let options = vec!["Option A".to_string(), "Option B".to_string()];
let start_time = Utc::now();
let end_time = start_time + Duration::hours(24);

let mut election = Election::new(
    "Test Election".to_string(),
    "Test Description".to_string(),
    options,
    start_time,
    end_time,
)?;

// Start the election
election.start()?;

// Cast a vote
let ballot = election.cast("voter1", 0)?;
let receipt = ballot.get_receipt();

// End election and tally votes
election.end()?;
let results = election.tally_votes()?;
```

## Security Considerations

1. **Key Management**: The system generates strong encryption keys, but proper key management in production is crucial.
2. **Voter Authentication**: This implementation focuses on the cryptographic aspects; production systems should implement strong voter authentication.
3. **Network Security**: When deploying, ensure all communications are encrypted using TLS.
4. **Audit Trail**: Consider implementing additional audit mechanisms for production use.

## Performance Considerations

The Rust implementation offers several advantages:
- Zero-cost abstractions for cryptographic operations
- Memory safety without runtime overhead
- Efficient big integer operations
- Thread safety through the type system
- Predictable performance characteristics

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## License

This project is licensed under the MIT License - see the LICENSE file for details.
