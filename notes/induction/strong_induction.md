---
layout: page
title: Strong induction
nav_order: 4
has_children: false
has_toc: false
parent: Induction 
grand_parent: Notes
---

## Another variant of induction 

Sometimes, the 
[previous version]({% link notes/induction/induction.md %}) 
is called weak induction compared to the following version 
where the you have a stronger assumption available for use 
in the induction step. 

**Theorem** (Strong induction). Let $P$ be a predicate 
on $n \in \mathbb{N}$. Assume we have some $n_0 \in \mathbb{N}$ 
with 
- a proof of $P(n_0)$ and 
- a proof, for all $n \geq n_0$, that 
$$
(\forall~ n_0 \leq k \leq n, P(k)) \to P(n+1)
$$

Then, we have a proof of $\forall~ n \geq n_0, P(n)$. 

{% proof %}
We make a new predicate 
$$
Q(n) = \forall~ n_0 \leq k \leq n, P(n)
$$
So a proof of $Q(n)$ is the same as proofs of each $P(k)$ for 
all $k$ between $n_0$ and $n$. Note that, for any $n \geq n_0$, 
we have $Q(n) \to P(n)$. <br><br> 
We use the usual version of induction to prove $Q(n)$ for all $n$. 
For the base case, we note that $Q(n_0) = P(n_0)$ which we 
have assumed we can prove. <br><br> 
For the induction step, we have assumed that we can prove 
$$
Q(n) \to P(n+1)
$$
But 
$$
Q(n+1) = Q(n) \land P(n+1)
$$
so we can prove $Q(n) \to Q(n+1)$. Appealing to (weak) induction, 
we can prove $Q(n)$ for all $n \geq n_0$. Since $Q(n)$ implies $P(n)$, 
we prove $P(n)$ for all $n \geq n_0$. 
{% endproof %}

A Lean-version of the proof is below. 
{% highlight lean %}
-- We will use this but will not prove it 
theorem based_induction {P : Nat → Prop} {n₀ : Nat} (base : P n₀) 
  (ind : ∀ n, n₀ ≤ n → P n → P (n+1)) (m : Nat) : n₀ ≤ m → P m := sorry 

-- This is the definition of Q(n) in the proof above
def StrongPred (P : Nat → Prop) (n₀ : Nat) : Nat → Prop := 
  fun n => ∀ k, n₀ ≤ k → k ≤ n → P k

-- Another two results we will use but not prove. You should 
-- recognize them from the above proof. 

-- To prove Q(n+1) it suffices to prove Q(n) and P(n+1) 
theorem sp_succ { P : Nat → Prop } { n₀ : Nat } (m : Nat) : 
  StrongPred P n₀ m ∧ P (m+1) → StrongPred P n₀ (m+1) := sorry 

-- Q(n) implies P(n) for all n
theorem strong_pred_imp {P : Nat → Prop} {n₀ : Nat} (h : n₀ ≤ n) : 
  StrongPred P n₀ n → P n := sorry 

theorem strong_induction {P : Nat → Prop} {n₀ : Nat} (base : P n₀) 
  (ind : ∀ n, StrongPred P n₀ n → P (n+1)) (m : Nat) : n₀ ≤ m → P m := by 
  -- We will want to apply based_induction to StrongPred
  -- The base case is n₀ 
  have base' : StrongPred P n₀ n₀ := by 
    intro k h₁ h₂ 
    have : k = n₀ := Nat.le_antisymm h₂ h₁ 
    rwa [this] 
  -- The induction step 
  have ind' : ∀ n, n₀ ≤ n → StrongPred P n₀ n → StrongPred P n₀ (n+1) := by 
    intro n _ h' 
    apply sp_succ n
    have p : P (n+1) := ind n h' 
    exact ⟨h',p⟩ 
  -- We appeal to based induction for StrongPred
  have SP : ∀ n, n₀ ≤ n → StrongPred P n₀ n := based_induction base' ind'
  -- Finally StrongPred P n₀ n → P n  
  exact fun h => strong_pred_imp h (SP m h)  
{% endhighlight %}

Why do we have this version? In general, $P(n) \to P(n+1)$ might be false 
where $(\forall k \leq n, P(k)) \to P(n+1)$ is true. We cannot use (weak) 
induction in this case but we can use strong induction. 

**Example**. The Tribonacci sequence is a sequence defined recursively by 
$$
a_0 = 0, a_1 = 0, a_2 = 1, a_n = a_{n-1} + a_{n-2} + a_{n-3} \text{ if } n \geq 3
$$
Let's show that $a_n \leq 2^{n-3}$ for all $n \geq 3$ using strong induction. 

Our base case is $n=3$. Then $a_3 = 1$ and $2^{3-3} = 1$. 

Now assume that we know that $a_k \leq 2^{k-3}$ for $3 \leq k \leq n$. We have 
$$
a_{n+1} = a_n + a_{n-1} + a_{n-2} \leq 2^{n-3} + 2^{n-4} + 2^{n-5} 
$$
as long as $n \geq 5$. We will need to cover the cases of $n=3,4$ separately. 
We will circle back to this but for right now assume that $n \geq 5$. 
Then, we can use the inequality above. We have 
$$
 2^{n-3} + 2^{n-4} + 2^{n-5} = 2^{n-5}(4 + 2 + 1) = 7 \cdot 2^{n-5} < 2^3 \cdot 2^{n-5} 
 = 2^{n-2}. 
$$
Thus $a_{n+1} \leq 2^{n-2}$ as long as $n \geq 5$. 

Assume that $n = 4$. Then we prove directly that $a_4 \leq 2$. We have 
$a_4 = a_3 + a_2 = 1 + 1 = 2 = 2^1$. 

Assume that $n = 5$. Then $a_5 = a_4 + a_3 + a_2 = 2 + 1 + 1 = 4 = 2^2$. 

These cover the missing cases above in the induction step. We can now 
appeal strong induction to get our conclusion.

In examples like the previous one, it makes sense to introduce another variant 
of induction: strong induction with multiple base cases. Here 
we cover some extra base cases before the induction step takes over. 

**Corollary**. Let $P$ be a predicate on $n \in \mathbb{N}$. Assume 
we have $n_0, n_1 \in \mathbb{N}$ with $n_0 \leq n_1$ with 
- proofs of each $P(n_0),\ldots,P(n_1)$ and 
- a proof that, for each $n \geq n_1$, 
$$
(\forall~ n_0 \leq k \leq n, P(k)) \to P(n+1)
$$

Then we have a proof of $\forall~ n \geq n_0, P(n)$. 

Let's do one more example of induction and recursion combined. 

**Definition**. For $n, k \in \mathbb{N}$, the _binomial coefficient_ $
\binom{n}{k}$ is defined recursively by 
$$
\binom{n}{0}= 1, \binom{0}{k+1} = 0, \binom{n+1}{k+1} = 
\binom{n}{k} + \binom{n}{k+1} 
$$

**Lemma**. If $k > n$, then $\binom{n}{k} = 0$. 

{% proof %}
We prove this via induction on $n$. The base case is $n = 0$. Since $k > 0$, 
we know that $k = k^\prime + 1$ for some $k^\prime \in \mathbb{N}$. Then 
by definition $\binom{0}{k^\prime + 1} = 0$. <br><br> 
Assume we know that $\binom{n}{k} = 0$ whenever $k > n$. Assume that 
$k > n+1$. We can again rewrite $k^\prime + 1 = k$. Then 
$$
\binom{n+1}{k^\prime+1} = \binom{n}{k^{\prime}} + \binom{n}{k^\prime +1}
$$
Since $k^\prime > n^\prime$ and $k^\prime + 1 > n$, both these terms are 
$0$ by definition. 
{% endproof %}

As an example, we compute 
$$
\binom{5}{2} = \binom{4}{1} + \binom{4}{2} 
= \binom{3}{0} + 2\binom{3}{1} + \binom{3}{2} 
= 3 \binom{3}{0} + 3\binom{2}{1} + \binom{2}{2} \\ 
= 3 \binom{3}{0} + 3 \binom{2}{0} + 4 \binom{1}{1} + \binom{1}{2} 
= 3 \binom{3}{0} + 3 \binom{2}{0} + 4 \binom{1}{0} + 4 \binom{0}{1} 
= 10 
$$

Where do these numbers come from and why the name? 

**Theorem** (Binomial formula). For any indeterminants $x$ and $y$ and any $n \in \mathbb{N}$ 
we have 
$$
(x+y)^n = \sum_{k=0}^n \binom{n}{k}x^{n-k}y^k 
$$

{% proof %}
We prove this using induction $n$. For the base case of $n=0$, we have $(x+y)^0 = 1$ and 
$$
\sum_{k=0}^0 \binom{n}{k} x^{-k} y^k = \binom{0}{0} = 1
$$
Assume that
$$
(x+y)^n = \sum_{k=0}^n \binom{n}{k} x^{n-k} y^k 
$$
Then 
$$
(x+y)^{n+1} = (x+y)(x+y)^n = (x+y) \sum_{k=0}^n \binom{n}{k} x^{n-k}y^k = \\
x \sum_{k=0}^n \binom{n}{k} x^{n-k}y^k + y \sum_{k=0}^n \binom{n}{k} x^{n-k}y^k = \\
\sum_{k=0}^n \binom{n}{k} x^{n+1-k}y^k + \sum_{k=0}^n \binom{n}{k} x^{n-k}y^{k+1} 
$$
Now we combine terms into a single sum. For $0 \leq j \leq n+1$, we get two 
contributions: $\binom{n}{j} x^{n+1-j}y^j$ from the first and $\binom{n}{j-1} x^{n+1-j} y^j$ 
from the second. Thus
$$
(x+y)^{n+1} = \sum_{j=0}^{n+1} \left( \binom{n}{j} + \binom{n}{j-1} \right) x^{n+1-j}y^j \\
= \sum_{j=0}^{n+1} \binom{n+1}{j} x^{n+1-j}y^j 
$$
Appealing to induction, we get our desired conclusion. 
{% endproof %}

**Example**. The Binomial Theorem allows access to many interseting formula about binomial 
coefficients. For example, if we take $x=y=1$, we get 
$$
2^n = \sum_{k=0}^n \binom{n}{k} 
$$
If we take $x = 1, y = -1$, then we get 
$$
0 = \sum_{k=0}^n (-1)^k \binom{n}{k} 
$$
