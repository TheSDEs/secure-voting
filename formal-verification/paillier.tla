-------------------------------- MODULE paillier --------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Voters,     \* Set of eligible voters
          Options,    \* Set of voting options
          BitLength   \* Security parameter for key generation

VARIABLES keys,       \* Cryptographic keys
          ballots,    \* Cast ballots
          votes,      \* Decrypted votes
          status      \* Election status

TypeOK == 
    /\ keys \in [n: Nat, g: Nat, lambda: Nat, mu: Nat]
    /\ ballots \in [voter: Voters, encrypted: Nat]
    /\ votes \in [Options -> Nat]
    /\ status \in {"Created", "Active", "Ended", "ResultsPublished"}

Init ==
    /\ keys = [n |-> 0, g |-> 0, lambda |-> 0, mu |-> 0]
    /\ ballots = {}
    /\ votes = [o \in Options |-> 0]
    /\ status = "Created"

\* Key Generation
GenerateKeys ==
    /\ status = "Created"
    /\ \E p, q \in {n \in Nat : n > 1} :
        /\ IsPrime(p) /\ IsPrime(q)
        /\ p # q
        /\ LET n == p * q
               lambda == LCM(p-1, q-1)
               g == n + 1
               mu == ModInverse(L(g^lambda, n), n)
           IN keys' = [n |-> n, g |-> g, lambda |-> lambda, mu |-> mu]
    /\ UNCHANGED <<ballots, votes, status>>

\* Ballot Casting
CastBallot(v, choice) ==
    /\ status = "Active"
    /\ v \in Voters
    /\ choice \in Options
    /\ ~\E b \in ballots : b.voter = v  \* No double voting
    /\ LET n == keys.n
           g == keys.g
           r == CHOOSE x \in 1..n-1 : GCD(x, n) = 1
           encrypted == (g^choice * r^n) % (n^2)
       IN ballots' = ballots \union {[voter |-> v, encrypted |-> encrypted]}
    /\ UNCHANGED <<keys, votes, status>>

\* Vote Tallying
TallyVotes ==
    /\ status = "Ended"
    /\ LET DecryptVote(c) ==
           LET n == keys.n
               lambda == keys.lambda
               mu == keys.mu
               u == (c^lambda % n^2)
               v == L(u, n)
           IN (v * mu) % n
       results == [o \in Options |->
           Cardinality({b \in ballots : DecryptVote(b.encrypted) = o})]
       IN votes' = results
    /\ status' = "ResultsPublished"
    /\ UNCHANGED <<keys, ballots>>

\* Security Properties
\* Privacy: No one can determine how a voter voted
Privacy ==
    \A v1, v2 \in Voters :
        \A b1, b2 \in ballots :
            b1.voter = v1 /\ b2.voter = v2 =>
                b1.encrypted # b2.encrypted

\* Integrity: Final tally correctly reflects all valid votes
Integrity ==
    status = "ResultsPublished" =>
        \A o \in Options :
            votes[o] = Cardinality({b \in ballots : 
                DecryptVote(b.encrypted) = o})

\* No double voting
NoDoubleVoting ==
    \A v \in Voters :
        Cardinality({b \in ballots : b.voter = v}) <= 1

\* Eligibility: Only eligible voters can cast ballots
Eligibility ==
    \A b \in ballots : b.voter \in Voters

THEOREM Safety ==
    []TypeOK /\ []Privacy /\ []Integrity /\ []NoDoubleVoting /\ []Eligibility

====
