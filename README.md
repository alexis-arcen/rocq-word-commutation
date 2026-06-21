# Proof of the Commutation Lemma in Rocq

*Status: Work in progress (currently refining the code and writing documentation).*

## Introduction
The purpose of this project is to prove the Commutation Lemma in Combinatorics on words, which is a corollary of the Fine-Wilf theorem. This lemma states that if two words over a finite alphabet commute, then they share a common root. Formally:

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
-   [./theory.md](./theory.md) : Mathematical proof of the Commutation Lemma.
-   [./assignment.md](./assignment.md) : Definitions and lemmas given by our professor.
-   [./proof_documented](./proof_documented.v) : Formal proof with documentation.
