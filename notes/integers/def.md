---
layout: page
title: The definition(s)
nav_order: 1
has_children: false
has_toc: false
parent: Integers 
grand_parent: Notes
---

## Building the $~\mathbb{Z}~$ from $~\mathbb{N}$

Intuitively, to go from $\mathbb{N}$, we just add in 
$-n$ for each $n \in \mathbb{N}$ with $n > 0$. We 
will see two different ways of handling this. 

**Grothendieck construction**. We start with $\mathbb{N}$ 
and consider the set $\mathbb{N} \times \mathbb{N}$ of 
ordered pairs of natural numbers. On this, we impose a 
relation. We write $(n_1,m_1) \sim (n_2,m_2)$ if 
$$ 
n_1 + m_2 = n_2 + m_1
$$

**Theorem**. This is an equivalence relation on $\mathbb{N} 
\times \mathbb{N}$. 

{% proof %}
We check that $\sim$ is reflexive. For any $(n,m)$, we 
have $(n,m) \sim (n,m)$ since $n + m = n + m$. 

Next we check symmetry. Assume that $(n_1,m_1) \sim 
(n_2,m_2)$. Then, by definition, we have 
$$
n_1 + m_2 = n_2 + m_1
$$
Flipping the equality we get
$$
n_2 + m_1 = n_1 + m_2
$$
so $(n_2,m_2) \sim (n_1,m_1)$. 

Now we check transitivity. Assume that $(n_1,m_1) \sim 
(n_2,m_2)$ and $(n_2,m_2) \sim (n_3,m_3)$. Then, we have 
$$
n_1 + m_2 = n_2 + m_1 \\
n_2 + m_3 = n_3 + m_2 
$$
So 
$$
n_1 + m_3 + n_2 = n_1 + n_3 + m_2 = n_1 + m_2 + n_3 = n_2 + m_1 + n_3 = 
n_3 + m_1 + n_2 
$$
We know that we cancel addition in $\mathbb{N}$ so we can conclude that 
$$
n_1 + m_3 = n_3 + m_1 
$$
{% endproof %}

Since we have an equivalence relation, we can form the quotient by that 
equivalence relation. 

**Definition**. The _integers_, denoted $\mathbb{Z}$, are the set of 
equivalence classes of $\mathbb{Z} := \mathbb{N} \times \mathbb{N}/\sim$. 

Ok, maybe this does not look like our familiar integers. Where is $-1$? 
Where are the $\mathbb{N}$'s even? 

**Definition**. We will let 
$$
\begin{aligned}
i : \mathbb{N} & \to \mathbb{Z} \\
n & \mapsto [(n,0)]
\end{aligned}
$$
and let 
$$
\begin{aligned}
i : \mathbb{N} & \to \mathbb{Z} \\
n & \mapsto [(0,n)]
\end{aligned}
$$

**Lemma**. 
- Both $i$ and $j$ are injective. 
- Every element of $\mathbb{Z}$ is in the image of $i$ or of $j$. 
- If $i(n) = j(m)$, then $n=m=0$. 

{% proof %}
Assume that $[(n,0)] = [(m,0)]$. Then we have seen that this is equivalent to 
$(n,0) \sim (m,0)$. So $n + 0 = m + 0$ or $n = m$. A similar argument shows 
that $j$ is injective. <br><br>

Let $[(n,m)]$ be an equivalence class. Assume that $n \geq m$. Then 
$$
n + 0 = (n-m) + m 
$$
So $(n,m) \sim (n-m,0)$ and $[(n,m)] = [(n-m,0)] = i(n-m)$. Now assume that $n \leq m$. 
Then 
$$
n + m-n = 0 + m 
$$
so $(n,m) \sim (0,m-n)$ and $[(n,m)] = [(0,m-n)] = j(m-n)$. <br><br>

Assume that $i(n) = j(m)$. Then $[(n,0)] = [(0,m)]$. So $(n,0) \sim (0,m)$. Thus, 
$$
n + m = 0 + 0 = 0 
$$
Since $n,m \in \mathbb{N}$, we have $n = m = 0$. 
{% endproof %}

Despite the unfamiliar definition, we see that $\mathbb{Z}$ is exactly 
two copies of $\mathbb{N}$ with their two $0$'s identified.

Furthermore, we can add elements of $\mathbb{Z}$! First, we start with 
componentwise addition on $\mathbb{N} \times \mathbb{N}$. 
$$
(n_1,m_1) + (n_2,m_2) := (n_1+n_2,m_1+m_2) 
$$

**Theorem**. The following is a well-defined function. 
$$
\begin{aligned}
\mathbb{Z} \times \mathbb{Z} & \to \mathbb{Z} \\
([(n_1,m_1)],[(n_2,m_2)]) & \mapsto [(n_1+n_2,m_1+m_2)]
\end{aligned}
$$

{% proof %}

{% endproof %}
