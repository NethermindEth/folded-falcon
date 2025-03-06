# Aggregated Falcon Signatures using LatticeFold

## Falcon overview
..Sign(sk, m)
r <- {0, 1}^k
c = H(pk, r, msg) e Rq
(s1, s2) <- [ (sk, c) -> (s1, s2) ~ D^2 ]
||(s1, s2)||₂ <= β
sig = (r, s2)

..Ver(pk = h, msg, sig)
c = H(pk, r, m)
s1 = c - s2 * h
return ||(s1, s2)||₂ <= β

mod p = 12289

## Possible system

Witness: Signature = (s1, s2)
Statement: c = Hash(msg, h, r)
Relation: s1 * h + s2 - c = 0  mod p ,
    AND (s1, s2) small

if we lift p to q, where q >> p, to avoid wraparound we add a (p * v) term
    s1 * h + s2 + p * v - c = 0  mod q
where v = -(s1 * h + s2 - c) / p  moq q
    AND v must be also small

### Some questions
- Need to account for degree difference?
- Replace random oracle (which creates r), by some concrete hash function?
  LaBRADOR dot system does not support but R1CS does?
