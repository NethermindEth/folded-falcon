# Aggregated Falcon Signatures using LatticeFold

## Falcon signature scheme overview
Falcon operates over a cyclotomic ring of degree $d = \{ 512, 1024 \}$ with modulus $p = 12289$.
 
### Sign(sk, m)
- Sample random salt: $r \leftarrow \{0, 1\}^k$
- Compute: $c = H(r, msg)$
- Generate signature components: $(s_1, s_2) \leftarrow [(sk, c) \rightarrow (s_1, s_2) \sim D^2]$
- Ensure norm constraint: $\|(s_1, s_2)\|_2  \leq \beta$
- Output signature: $sig = (r, s_2)$

### Ver(pk = h, msg, sig)
- Recompute: $c = H(r, msg)$
- Compute: $s_1 = c - s_2  \cdot h$
- Verify norm constraint: $\|(s_1, s_2)\|_2  \leq \beta$

## Aggregation system

**Witness**: Signature $(s_1, s_2)$
**Statement**: $c = Hash(r, msg)$
**Relation**: $s_1  \cdot h + s_2 - c \equiv 0  \pmod{p}$ and $(s_1, s_2)$ are small

If we lift $p$ to $q$, where $q \gg p$, to avoid wraparound we add a $p \cdot v$ term: $s_1  \cdot h + s_2 + p \cdot v - c \equiv 0  \pmod{q}$
where, $v = -(s_1  \cdot h + s_2 - c) / p \bmod q$ and $v$ must also be small

### Used ring

## References

## License

Apache 2.0

(the license is also applied to the commits done before the license was committed)
