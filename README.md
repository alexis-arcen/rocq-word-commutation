# Proof of the Commutation Lemma in Rocq

## Introduction
The purpose of this project is to prove the Commutation Lemma in word theory, which is a corollary of the Fine-Wilf theorem. This lemma states that if two words over a finite alphabet commute, then they share a common root. Formally:

Let $\Sigma$ be a finite alphabet. 

$$
\forall u,v \in \Sigma^* ,
\quad
uv = vu
\implies
\exists w \in \Sigma^* ,
\exists n,m \in \mathbb{N}
\text{ such that }
u = w^n 
\text{ and }
v = w^m.
$$

> [!NOTE]
> The Commutation Lemma is a specific case of the Fine-Wilf Theorem, which is
> often viewed as a "strong" version of the Periodicity Lemma. It states that if a word
> $w$ has $p$ and $q$ as periods and $\left| w \right| \geqslant p+q - gdc(p,q)$, then $gdc(p,q)$ is a period of $w$.

## Project Structure
-   `proof/` : Contains the formal proof in Rocq (`.v` files).
-   [Mathematical theory](./theory.md) : Mathematical proof of the Commutation Lemma.
-   [Rocq Implementation](./docs/rocq_details.md) : Technical explanation of the formal proof and tactics used.

> [!IMPORTANT]
> This is a supervised project; the outline of the main proof, along with several key
> lemmas, were provided by our instructor. Therefore, all provided materials will be
> explicitly credited. See [Rocq Implementation](./docs/rocq_details.md) for more details.
