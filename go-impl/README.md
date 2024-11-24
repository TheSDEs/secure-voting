# Secure Voting System (Go Implementation)

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

1. **Cryptographic Layer** (`pkg/crypto/paillier.go`)
   - Implementation of the Paillier cryptosystem
   - Key generation, encryption, and decryption
   - Homomorphic addition of encrypted votes

2. **Voting System** (`pkg/voting/`)
   - `ballot.go`: Ballot creation and verification
   - `election.go`: Election management and vote tallying

## Security Features

- Homomorphic encryption ensures votes remain encrypted during tallying
- Voter anonymity through hashed voter IDs
- Verifiable voting receipts
- Prevention of double voting
- Secure key generation and management

## Getting Started

### Prerequisites

- Go 1.20 or later
- Dependencies (managed via Go modules):
  - github.com/stretchr/testify
  - golang.org/x/crypto

### Installation

1. Clone the repository
2. Install dependencies:
   ```bash
   go mod download
   ```

### Running Tests

```bash
go test ./...
```

## Usage Example

```go
// Create a new election
options := []string{"Option A", "Option B", "Option C"}
startTime := time.Now()
endTime := startTime.Add(24 * time.Hour)

election, err := voting.NewElection("Test Election", "Test Description", options, startTime, endTime)
if err != nil {
    log.Fatal(err)
}

// Start the election
err = election.Start()
if err != nil {
    log.Fatal(err)
}

// Cast a vote
ballot, err := election.Cast("voter1", 0)
if err != nil {
    log.Fatal(err)
}

// Get voter receipt
receipt := ballot.GetVoterReceipt()

// End election and tally votes
err = election.End()
if err != nil {
    log.Fatal(err)
}

results, err := election.TallyVotes()
if err != nil {
    log.Fatal(err)
}
```

## Security Considerations

1. **Key Management**: The system generates strong encryption keys, but proper key management in production is crucial.
2. **Voter Authentication**: This implementation focuses on the cryptographic aspects; production systems should implement strong voter authentication.
3. **Network Security**: When deploying, ensure all communications are encrypted using TLS.
4. **Audit Trail**: Consider implementing additional audit mechanisms for production use.

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## License

This project is licensed under the MIT License - see the LICENSE file for details.
