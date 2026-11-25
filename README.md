# Population Size versus Crossover Probability: Dichotomies for the $(\mu+1)$ GA on $\mathrm{Jump}_k$

A Lean 4 formalization of lower and upper bounds on the expected optimization time of
the $(\mu+1)$ genetic algorithm on $\mathrm{Jump}_k$, with and without avoidance of
replications. It is a [Lax Archive](https://laxarchive.org) submission with the id
[`lax-637351`](https://laxarchive.org/lax-637351/).

## Abstract

We present dichotomy theorems for the ${(\mu+1)}$ GA on $\mathrm{Jump}_k$ with and without
avoidance of replications. For constant jump size ${k\ge2}$ and uniform initialization, we
provide population thresholds, depending on the problem size $n$ and the crossover
probability $p_c$, that separate efficient from inefficient optimization times $T$.

We find that, without avoidance of replications, frequent crossover is beneficial. This contradicts
previous belief and, in particular, implies that Theorem 6 of Jansen and Wegener (2002) is
false. In contrast, with avoidance of replications, rare crossover is beneficial, as earlier
work suggested.

**Theorem 1 (Without avoidance of replications).** Let ${k\ge2}$ be a constant and ${2\le\mu\le n^{o(1)}}$.\
  (i) If ${\mu=o(\log(n)/p_c)}$, then ${\mathbb E[T]\ge n^{k-o(1)}}$.\
  (ii) If ${\mu=\omega(\log(n)/p_c)}$, then ${\mathbb E[T]=O(\mu n)}$.

**Theorem 2 (With avoidance of replications).** Let ${k\ge2}$ be a constant and ${\mu\ge2}$.\
  (i) If ${p_c=\omega(1/n)}$ and ${\mu=o(\log(np_c))}$, then ${\mathbb E[T]\ge(np_c)^{k-o(1)}/p_c}$.\
  (ii) If ${p_c=\omega(1/n)}$ and ${\mu=\omega(\log(np_c))}$, then ${\mathbb E[T]=O(\mu n\log(1+1/p_c))}$.\
  (iii) If ${p_c=O(1/n)}$, then ${\mathbb E[T]=O(\mu n\log n+1/p_c)}$.

**Why Theorem 6 of Jansen and Wegener (2002) is false.** For ${k=O(\log n)}$, Theorem 6 claims
that the ${(\mu+1)}$ GA without avoidance of replications, with ${p_c\le1/(Kkn)}$ (where $K$ is a
sufficiently large constant) and ${k\log^2n\le\mu\le n^{O(1)}}$, satisfies
${\mathbb E[T]=O(\mu n^2k^3+4^k/p_c)}$. Ignoring constant factors, the theorem allows ${\mu\approx k\log^2n}$
and ${p_c\approx1/(kn)}$. In this
setting, the population size $\mu$ is smaller than the threshold ${\log(n)/p_c\approx kn\log n}$
by a factor of about $n/\log n$, which implies ${\mu=o(\log(n)/p_c)}$. Hence, for constant $k$,
Theorem 1(i) gives ${\mathbb E[T]\ge n^{k-o(1)}}$. But Theorem 6 claims ${\mathbb E[T]=O(n^2\log^2n)}$, which is
asymptotically smaller for ${k\ge3}$.

**AI disclosure.** The proofs were found using GPT 6.1 Sol and Claude Opus 5.5, and the
results were formalized in Lean using GPT 6.2 Sol and Claude Opus 5.5.

## Status

All five results are proved in Lean 4 (`v4.33.0`) with mathlib (commit `db584cd`). The proofs
contain no `sorry`, and they depend only on Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound`. The submission passes a full local `lax build`.

## Building

With the [Lax CLI](https://www.npmjs.com/package/lax-archive) (`npm install -g lax-archive`),
run from the repository root:

```sh
lax build .
```

Lax provides the pinned Lean toolchain and a prebuilt mathlib. A build from scratch with a single
Lean thread took about 13 minutes on our machine, with a peak memory use of about 3.4 GB.

## License

Apache License 2.0; see [`LICENSE`](LICENSE).
