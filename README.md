# Proof of the Commutation Lemma in Rocq

## Introduction
The purpose of this university project is to prove the Commutation Lemma (Lyndon and Schützenberger) in Combinatorics on words, which is a corollary of the Fine-Wilf theorem. This lemma states that if two words over a finite alphabet commute, then they share a common root. Formally:

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

## Project Structure
-   [./theory.md](./theory.md) : Mathematical proof of the Commutation Lemma.
-   [./assignment.v](./assignment.v) : Definitions and lemmas given by our professor.
-   [./proof.v](./proof.v) : Formal proof.
-   [./proof_documented.v](./proof_documented.v) : Formal proof with documentation.
