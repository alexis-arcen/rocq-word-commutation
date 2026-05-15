# Mathematical proof of the Commutation Lemma

This proof will be carried out by induction on the maximum sum of the total lengths of the words.

Let $\Sigma$ be a finite alphabet. Let's prove the following statement by induction on $k$:

$$
\forall u,v \in \Sigma^* ,
\forall k \in \mathbb{N} ,
\quad
uv = vu
\text{ and }
\left|u\right| + \left|v\right| \leqslant k
\implies
\exists w \in \Sigma^* ,
\exists n,m \in \mathbb{N}
\text{ such that }
u = w^n 
\text{ and }
v = w^m.
$$


**Base case:** If $\left|u\right| + \left|v\right| = 0$ then $\left|u\right| = \left|v\right| = 0$ by definition of the length of a word.
This implies that $u=v=\epsilon$. Therefore by choosing $w=\epsilon$, and $n=m=1$ for example, we have $u=v=w^n=w^m$. 

**Inductive step:** We assume the following Inductive Hypothesis (IH) for a given $k \gt 0$ : $(uv=vu \land \left|u\right| + \left|v\right| \le k) \implies \exists w \in \Sigma^* , 
\exists n,m \in \mathbb{N} \text{ such that } u = w^n \text{ and } v = w^m.$ We want to prove this property given $k+1$.
