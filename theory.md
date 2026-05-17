# Mathematical proof of the Commutation Lemma

This proof will be carried out by induction on the total sum of lengths of the words.

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

**Proof.**

**Base case:** If $\left|u\right| + \left|v\right| = 0$ then $\left|u\right| = \left|v\right| = 0$ by definition of the length of a word.
This implies that $u=v=\epsilon$. Therefore by choosing $w=\epsilon$, and $n=m=1$ for example, we have $u=w^n$ and $v=w^m$. Thus, the property holds for $k=0$. 

**Inductive step:** We assume the following Inductive Hypothesis (IH) for a given $k \gt 0$ : $(uv=vu \land \left|u\right| + \left|v\right| \le k) \implies \exists w \in \Sigma^* , 
\exists n,m \in \mathbb{N} \text{ such that } u = w^n \text{ and } v = w^m.$ We want to prove this property holds for $k+1$. To do so, we proceed by cases on the parity of $\left|u\right| - \left|v\right|$. Furthermore, the case where $u=\epsilon$ or $v=\epsilon$ being trivial, we shall assume that $\left|u\right| \gt 0$ and $\left|v\right| \gt 0$.

**Case 1:** If $\left|u\right| = \left|v\right|$ and $uv=vu$, then $u=v$. Therefore by choosing $w=u$ and $n=m=1$, we have $u=w^n$ and $v=w^m$. 

**Case 2:** If $\left|u\right| \gt \left|v\right|$ and $uv=vu$, then there exists a word $u' \in \Sigma^*$ such that $u=vu'$. Firstly, by replacing $u$ by $vu'$ in $uv=vu$ we deduct $uv=vu \iff vu'v=vvu' \iff u'v=vu'$. Secondly, if $\left|u\right| \gt \left|u'\right|$, then we deduct the following sequence:
  
$$
\begin{aligned}
\left|u\right| + \left|v\right| &\leqslant k+1 \\
\left|v\right| + \left|u'\right| + \left|v\right| &\leqslant k+1 \\
\left|u'\right| + \left|v\right| \lt \left|v\right| + \left|u'\right| + \left|v\right| &\leqslant k+1 \\
\left|u'\right| + \left|v\right| &\lt k+1 \\
\left|u'\right| + \left|v\right| &\leqslant k
\end{aligned}
$$

Finally, since $u'v=vu'$ and $\left|u'\right| + \left|v\right| \leqslant k$, the $IH$ applied to $u'$ and $v$ implies that there exists $w \in \Sigma^*$ and $n,m \in \mathbb{N}$ such that $u'=w^n$ and $v=w^m$. Therefore, since $u=vu'$, $u=w^m.w^n=w^{m+n}$ which concludes the proof for this case.

**Case 3:** If $\left|u\right| \lt \left|v\right|$ and $uv=vu$, then we can use the method as stated in _Case 2_ symmetrically, by choosing $v=v'u$.

By the principle of mathematical induction, the statement holds for all $k \ge 0. \qquad \square$
