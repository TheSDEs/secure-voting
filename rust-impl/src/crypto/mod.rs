use num_bigint::{BigInt, RandBigInt, BigUint, ToBigInt};
use num_traits::{One, Zero};
use num_integer::Integer;
use rand::thread_rng;
use std::error::Error;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum CryptoError {
    #[error("message too large")]
    MessageTooLarge,
    #[error("ciphertext too large")]
    CiphertextTooLarge,
    #[error("invalid key generation parameters")]
    InvalidKeyGeneration,
    #[error("invalid parameters: {0}")]
    InvalidParameters(String),
}

pub struct KeyPair {
    pub public: PublicKey,
    pub private: PrivateKey,
}

#[derive(Clone)]
pub struct PublicKey {
    pub n: BigUint,
    pub g: BigUint,
    pub n_square: BigUint,
}

pub struct PrivateKey {
    lambda: BigUint,
    mu: BigUint,
    pub public: PublicKey,
}

impl KeyPair {
    pub fn generate(bits: u32) -> Result<Self, Box<dyn Error>> {
        let mut rng = thread_rng();
        
        // Generate two random prime numbers
        let p = loop {
            let p = rng.gen_biguint((bits / 2) as u64);
            if is_prime(&p) {
                break p;
            }
        };

        let q = loop {
            let q = rng.gen_biguint((bits / 2) as u64);
            if is_prime(&q) && q != p {
                break q;
            }
        };

        let n = &p * &q;
        let lambda = lcm(&(p - BigUint::one()), &(q - BigUint::one()));
        let g = &n + BigUint::one();
        let n_square = &n * &n;
        let mu = {
            let g_lambda = mod_pow(
                &g.to_bigint().unwrap(),
                &lambda.to_bigint().unwrap(),
                &n_square.to_bigint().unwrap()
            );
            let l = PrivateKey::l(&g_lambda, &n.to_bigint().unwrap())?;
            match mod_inverse(&l, &n.to_bigint().unwrap()) {
                Some(mu) => mu.to_biguint().unwrap(),
                None => return Err(CryptoError::InvalidKeyGeneration.into()),
            }
        };

        let public = PublicKey {
            n: n.clone(),
            g,
            n_square,
        };

        let private = PrivateKey {
            lambda,
            mu,
            public: public.clone(),
        };

        Ok(KeyPair { public, private })
    }
}

impl PublicKey {
    pub fn encrypt(&self, m: &BigInt) -> Result<BigInt, CryptoError> {
        let n_int = self.n.to_bigint().unwrap();
        if m >= &n_int {
            return Err(CryptoError::MessageTooLarge);
        }

        let r = generate_coprime(&self.n);
        let g_int = self.g.to_bigint().unwrap();
        let n_square_int = self.n_square.to_bigint().unwrap();
        
        let gm = mod_pow(&g_int, m, &n_square_int);
        let rn = mod_pow(&r.to_bigint().unwrap(), &n_int, &n_square_int);
        
        Ok((gm * rn) % n_square_int)
    }

    pub fn add(&self, c1: &BigInt, c2: &BigInt) -> BigInt {
        (c1 * c2) % self.n_square.to_bigint().unwrap()
    }
}

impl PrivateKey {
    pub fn new(p: BigUint, q: BigUint) -> Result<Self, CryptoError> {
        let n = &p * &q;
        let lambda = lcm(&(p - BigUint::one()), &(q - BigUint::one()));
        let g = &n + BigUint::one();
        let n_square = &n * &n;
        let mu = Self::compute_mu(&lambda, &n)?;

        Ok(PrivateKey {
            lambda,
            mu,
            public: PublicKey {
                n,
                g,
                n_square,
            }
        })
    }

    fn compute_mu(lambda: &BigUint, n: &BigUint) -> Result<BigUint, CryptoError> {
        let n_int = n.to_bigint().unwrap();
        let lambda_int = lambda.to_bigint().unwrap();
        let n_square_int = &n_int * &n_int;
        let g_lambda = mod_pow(&(&n_int + BigInt::one()), &lambda_int, &n_square_int);
        let l = Self::l(&g_lambda, &n_int)?;
        
        match mod_inverse(&l, &n_int) {
            Some(mu) => Ok(mu.to_biguint().unwrap()),
            None => Err(CryptoError::InvalidParameters("Failed to compute mu".into()))
        }
    }

    pub fn decrypt(&self, c: &BigInt) -> Result<BigInt, CryptoError> {
        let n_square_int = self.public.n_square.to_bigint().unwrap();
        if c >= &n_square_int {
            return Err(CryptoError::CiphertextTooLarge);
        }

        let lambda_int = self.lambda.to_bigint().unwrap();
        let n_int = self.public.n.to_bigint().unwrap();
        let mu_int = self.mu.to_bigint().unwrap();

        let u = mod_pow(c, &lambda_int, &n_square_int);
        let l = Self::l(&u, &n_int)?;
        Ok((l * mu_int) % n_int)
    }

    fn l(u: &BigInt, n: &BigInt) -> Result<BigInt, CryptoError> {
        if u <= &BigInt::zero() {
            return Err(CryptoError::InvalidParameters("Input must be positive".into()));
        }
        Ok((u - BigInt::one()) / n)
    }
}

fn is_prime(n: &BigUint) -> bool {
    if n <= &BigUint::one() {
        return false;
    }
    
    // Simple primality test using trial division
    let small_primes = [2u32, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];
    for &p in &small_primes {
        if n % p == BigUint::zero() {
            return n == &BigUint::from(p);
        }
    }
    
    // Miller-Rabin primality test
    let mut d = n - BigUint::one();
    let mut r = 0;
    
    while &d % 2u32 == BigUint::zero() {
        d /= 2u32;
        r += 1;
    }
    
    // Number of iterations for Miller-Rabin test
    let k = 20;
    let mut rng = thread_rng();
    
    'outer: for _ in 0..k {
        let a = loop {
            let a = rng.gen_biguint_below(n);
            if a > BigUint::one() {
                break a;
            }
        };
        
        let mut x = a.modpow(&d, n);
        if x == BigUint::one() || x == n - BigUint::one() {
            continue;
        }
        
        for _ in 0..r-1 {
            x = (&x * &x) % n;
            if x == n - BigUint::one() {
                continue 'outer;
            }
        }
        
        return false;
    }
    
    true
}

fn generate_coprime(n: &BigUint) -> BigUint {
    let mut rng = thread_rng();
    loop {
        let r = rng.gen_biguint_below(n);
        if r.gcd(n) == BigUint::one() {
            return r;
        }
    }
}

fn lcm(a: &BigUint, b: &BigUint) -> BigUint {
    a * b / a.gcd(b)
}

fn mod_pow(base: &BigInt, exponent: &BigInt, modulus: &BigInt) -> BigInt {
    let mut result = BigInt::one();
    let mut base = base.clone();
    let mut exp = exponent.clone();

    while !exp.is_zero() {
        if &exp % 2i32 == BigInt::one() {
            result = (&result * &base) % modulus;
        }
        base = (&base * &base) % modulus;
        exp /= 2i32;
    }

    result
}

fn mod_inverse(a: &BigInt, m: &BigInt) -> Option<BigInt> {
    let mut t = BigInt::zero();
    let mut newt = BigInt::one();
    let mut r = m.clone();
    let mut newr = a.clone();

    while !newr.is_zero() {
        let quotient = &r / &newr;
        let temp_t = t.clone();
        t = newt.clone();
        newt = temp_t - &quotient * &newt;
        let temp_r = r.clone();
        r = newr.clone();
        newr = temp_r - quotient * newr;
    }

    if r > BigInt::one() {
        return None;
    }
    if t < BigInt::zero() {
        t = t + m;
    }
    Some(t)
}
