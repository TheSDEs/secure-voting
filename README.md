# Secure Voting System

A secure and verifiable electronic voting system implemented in both Rust and Go, utilizing the Paillier homomorphic encryption scheme. This system ensures voter privacy, prevents double voting, and provides verifiable vote tallying.

## Project Overview

This project implements a secure voting system with the following key features:

- **Homomorphic Encryption**: Uses the Paillier cryptosystem for secure vote encryption and tallying
- **Dual Implementation**: Available in both Rust and Go for comparison and flexibility
- **Formal Verification**: Includes formal proofs of security properties using Coq
- **Privacy Preserving**: Ensures voter anonymity while maintaining vote integrity
- **Verifiable**: Provides mechanisms to verify vote counting without compromising privacy

### Directory Structure

```
secure-voting/
├── rust-impl/               # Rust implementation
│   ├── src/
│   │   ├── crypto/         # Cryptographic operations
│   │   ├── voting/         # Voting system logic
│   │   └── lib.rs          # Library root
│   ├── Cargo.toml          # Rust dependencies
│   └── tests/              # Integration tests
├── go-impl/                # Go implementation
│   ├── pkg/
│   │   ├── crypto/         # Cryptographic operations
│   │   └── voting/         # Voting system logic
│   ├── go.mod              # Go dependencies
│   └── tests/              # Integration tests
└── formal-verification/    # Formal proofs
    ├── paillier.tla        # TLA+ specifications
    ├── PaillierProof.v     # Coq proofs
    └── protocol.pv         # ProVerif protocol verification
```

## Features

1. **Cryptographic Security**
   - Paillier homomorphic encryption for secure vote counting
   - Zero-knowledge proofs for vote validity
   - Secure key generation and management

2. **Vote Privacy**
   - Anonymous vote casting
   - Encrypted ballot storage
   - Privacy-preserving vote tallying

3. **Vote Integrity**
   - Prevention of double voting
   - Verifiable vote counting
   - Tamper-evident ballot storage

4. **System Properties**
   - Distributed architecture support
   - Scalable vote processing
   - Audit trail generation

## Implementation Details

### Rust Implementation

The Rust implementation prioritizes memory safety and type-level guarantees:

```rust
// Example vote casting
pub fn cast_vote(&mut self, voter_id: String, choice: usize) -> Result<(), VotingError> {
    if self.status != ElectionStatus::Started {
        return Err(VotingError::NotStarted);
    }
    // ... vote processing logic
}
```

### Go Implementation

The Go implementation focuses on simplicity and concurrent processing:

```go
// Example vote casting
func (e *Election) Cast(voterID string, choice int) (*Ballot, error) {
    if e.Status != Active {
        return nil, errors.New("election is not active")
    }
    // ... vote processing logic
}
```

## Formal Verification

The system's security properties are formally verified using:

1. **Coq Proofs**
   - Vote privacy
   - Double voting prevention
   - Tally correctness

2. **TLA+ Specifications**
   - System state transitions
   - Invariant properties
   - Liveness conditions

3. **ProVerif Protocol Verification**
   - Security protocol analysis
   - Attack scenario verification
   - Privacy properties

## Getting Started

### Prerequisites

- Rust (latest stable version)
- Go 1.19 or later
- Coq 8.16 or later (for formal verification)

### Installation

1. Clone the repository:
```bash
git clone https://github.com/yourusername/secure-voting.git
cd secure-voting
```

2. Build Rust implementation:
```bash
cd rust-impl
cargo build --release
```

3. Build Go implementation:
```bash
cd ../go-impl
go build ./...
```

### Running Tests

Rust tests:
```bash
cd rust-impl
cargo test
```

Go tests:
```bash
cd go-impl
go test ./...
```

## Usage

1. **Start an Election**
```rust
let election = Election::new(
    "Presidential Election 2024",
    "National Presidential Election",
    vec!["Candidate A", "Candidate B"],
)?;
election.start()?;
```

2. **Cast Votes**
```rust
election.cast_vote("voter123", 0)?; // Vote for Candidate A
```

3. **End Election and Tally**
```rust
election.end()?;
let results = election.tally_votes()?;
```

## Security Considerations

1. **Key Management**
   - Secure key generation and storage
   - Proper key distribution
   - Regular key rotation

2. **Vote Privacy**
   - Anonymous vote submission
   - Encrypted storage
   - Privacy-preserving tallying

3. **System Security**
   - Access control
   - Audit logging
   - DDoS protection

## Contributing

1. Fork the repository
2. Create a feature branch
3. Commit your changes
4. Push to the branch
5. Create a Pull Request

## Acknowledgments

- The Paillier cryptosystem implementation is based on the paper "Public-Key Cryptosystems Based on Composite Degree Residuosity Classes" by Pascal Paillier
- Formal verification methodology inspired by the work of various researchers in the field of electronic voting systems
