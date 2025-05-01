# Aggregated Falcon Signatures using LatticeFold

## Falcon signature scheme overview
Falcon operates over a cyclotomic ring of degree $d = \\{ 512, 1024 \\}$ with modulus $p = 12289$.

### Signing (secret key, msg)
1. Sample random salt: $r \leftarrow \\{0, 1\\}^k$
2. Compute: $c = H(r, msg)$
3. Generate signature components: $(s_1, s_2) \leftarrow [(sk, c) \rightarrow (s_1, s_2) \sim D^2]$
4. Ensure norm constraint: $\|(s_1, s_2)\|_2  \leq \beta$
5. Output signature: $sig = (r, s_1, s_2)$

### Verify (public key $= h$, msg, sig)
1. Recompute: $c = H(r, msg)$
2. Compute: $s_1 = c - s_2  \cdot h$
3. Verify $\ell^2$-norm constraint: $\|(s_1, s_2)\|_2  \leq \beta$

## Aggregation system

**Witness**: Signature $(s_1, s_2)$. Given that we cannot prove $r$'s validity, we must move it to the statement.

**Statement**: $h$, $c = Hash(r, msg)$

**Relation**: $s_1  \cdot h + s_2 - c \equiv 0  \pmod{p}$,and $(s_1, s_2)$ are small

If we want to employ another modulus $q$, where $q \gg p$, we add a lifting term $p \cdot v$ term. The relation above becomes,

**Relation, lifted**:  $s_1  \cdot h + s_2 + p \cdot v - c \equiv 0  \pmod{q}$,
where, $v = -(s_1  \cdot h + s_2 - c) / p \bmod q$ and $v$ must also be small.

## Employing LatticeFold

The LatticeFold implementation mainly operates using cyclotomic polynomials in NTT form. Employed rings must implement the trait `SuitableRing`.

The Falcon modulus $p = 12289$ does not provide enough security in LatticeFold, so the lifting mechanism described above is employed.

### Constraint system

R1CS is used to represent the system constraints, which is then converted into a CCS system used as required in LatticeFold.

The above relation (lifted) is proven, with the l2-norm bound check being approximated using bit-decomposition, that is, the l2-norm squared $\|(s_1, s_2)\|_2^2$ is proven to be representable using $\left\lceil log_2 \beta^2 \right\rceil$ bits.

### Supported rings

Out of the [available configured `stark-rings`](https://github.com/NethermindEth/stark-rings/tree/main/ring/src/cyclotomic_ring/models), only the Frog ring (degree $d\prime = 16$, modulus $q \approx 2^{64}$) is currently supported.

For this, the split-ring homomorphism is employed, where a Falcon polynomial of degree $d$ is mapped into $k = d/d\prime$ smaller polynomials. Each of these smaller polynomials is a Frog polynomial ring.

For the Frog ring, employed in a folding-1-signature constraint system (R1CS) we have 2237 constraints and 3325 inputs. Out of these inputs, 3260 are witness values.

## Development

This repository includes pre-commit/pre-push Git hooks managed in the `.githooks/` directory.
These hooks help ensure code quality and consistency (e.g., formatting, linting).

To enable these hooks, run the following command in your terminal:

```bash
git config core.hooksPath .githooks
```

This command needs to be run only once per repository clone.

## Performance

Run available benchmarks using `cargo bench`.

## References

Implementation inspired by,

- [LatticeFold: A Lattice-based Folding Scheme and its Applications to Succinct Proof Systems](https://eprint.iacr.org/2024/257);
- [Shorter Lattice-Based Group Signatures via "Almost Free" Encryption and Other Optimizations](https://eprint.iacr.org/2021/1575);
- [Aggregating Falcon Signatures with LaBRADOR](https://eprint.iacr.org/2024/311).

## License

Apache 2.0

(the license is also applied to the commits done before the license was committed)
