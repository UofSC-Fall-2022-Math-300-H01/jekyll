---
layout: page
title: Mod m 
nav_order: 3
has_children: false
has_toc: false
parent: Integers 
grand_parent: Notes
---

## Arithmetic with remainders 

We now have $\mathbb{Z}$ at our disposal. Conceptually, the 
integers are a wonderful tool. Practically, we can only 
even consider finitely many things. 

For example, on your computer 
now, there is only a finite amount of memory. It is a very 
large collection of what can be viewed as switches. To store 
data, these switches can be in the on position or the off position. 
Suppose we have $b$ switches. Suppose we have a number $n$ that 
we wish to store in memory. How can we do that with switches? 

A question we can ask about $n$ to help pin it down is whether it 
is even or odd. Since it is a binary choice, it can be captured completely 
using a single switch. To store this information, we just remember the 
value $n \mod 2$. 

While knowing $0$ versus $1$ (for even vs odd) is useful, we generally 
want to work with larger numbers. Let $\epsilon_0$ be the remainder 
from dividing $m$ by $2$. Then $m \equiv \epsilon_0 \mod 2$ and 
$ m - \epsilon_0 = 2m_1$ for some $m_1$. 

This $m_1$ itself could be even or odd. Let $\epsilon_1$ be its remainder 
when divided by $2$. Then 
$$
m - \epsilon_0 - 2\epsilon_1 = 4m_2
$$
So 
$$ 
m \equiv \epsilon_0 + 2 \epsilon_1 \mod 4
$$

We can continue this process to write 
$$
m \equiv \sum_{j = 0}^{n-1} \epsilon_j 2^j \mod 2^n 
$$
and each $\epsilon_j \in \lbrace 0,1 \rbrace$.

Since $\equiv_m$ is an equivalence relation, we can form its quotient. 

**Definition**. The _integers mod $m$_, denoted $\mathbb{Z}/m\mathbb{Z}$, 
are the quotient 
$$
\mathbb{Z}/m\mathbb{Z} := \mathbb{Z}/\equiv_m
$$
of $\mathbb{Z}$ by the equivalence relation $\equiv_m$. 

Remember that this means that 
$$
\mathbb{Z}/m\mathbb{Z} = \lbrace [n] \mid n \in \mathbb{Z} \rbrace
$$
where each 
$$
[n] = \lbrace n' \mid n' \equiv n \mod m \rbrace 
$$
are equivalence classes.

Recall that the _division algorithm_ on $\mathbb{Z}$ takes in $n 
\in \mathbb{Z}$ and $m \in \mathbb{N}$ and outputs $q_n,r_n \in \mathbb{Z}$ with 
$$
n = q_n m + r_n
$$ 
and 
$$
0 \leq r_n < m 
$$
Moreover, $q_n$ and $r_n$ along with $m$ uniquely determine $m$. 

**Lemma**. Let $m \in \mathbb{N}$. The function 
$$
\begin{aligned}
r : \mathbb{Z} & \to \mathbb{N} \\ 
n & \mapsto r_n 
\end{aligned}
$$
descends to 
$$
\overline{r} : \mathbb{Z}/m\mathbb{Z} \to \mathbb{N}
$$
Moreover, it is a bijection with its image $\lbrace n \mid 0 \leq n < m \rbrace$. 

{% proof %}
To show that a function descends to the quotient by an equivalence 
relation, we need to show that it is _constant_ on equivalence classes, ie 
whenever $n \equiv n' \mod m$ we have $r_n = r_{n'}$. 

By definition, we have $n - n' = cm$ for some $c$. Thus, 
$$
q_n m + r_n - (q_{n'}m + r_{n'}) = cm 
$$
or 
$$
r_n - r_{n'} = (c - q_{n'} + q_n)m
$$
In other words, $r_n - r_{n'}$ is divisible by $m$. But since $0 \leq r_n, r_{n'} < m$, 
we have 
$$
-m < r_n - r_{n'} < m 
$$
The only number strictly between $-m$ and $m$ that is divisible by $m$ is $0$. So 
$$
r_n = r_{n'}
$$
So we see that $r$ is constant on equivalence classes. 

Since $r_j = j$ for $0 \leq j < m$, we see that the image of $r$ is 
$\lbrace n \mid 0 \leq n < m \brace$. 

To finish, we check that $\overline{r}$ is injective. Assume that $r_n = r_{n'}$. 
Then 
$$
n - n' = q_n m + r_n - (q_{n'}m + r_n) = (q_n - q_{n'})m 
$$
so $n \equiv n' \mod m$. Thus, $\overline{r}$ is injective and a bijection 
onto its image. 
{% endproof %}

**Example**. Let's take $m=5$. The previous lemma says that 
$$
\mathbb{Z}/5\mathbb{Z} = \lbrace [0], [1], [2], [3], [4] \rbrace 
$$
We can figure out which box to place $n \in \mathbb{Z}$ into mod $5$ by 
determining its remainder after division by $5$. So $22 = 4\cdot 5 + 2$ 
and $[22] = [2]$. 

We can also transport arithmetic from $\mathbb{Z}$ to $\mathbb{Z}/m\mathbb{Z}$. 

**Definition/Lemma**. We add two elements of $\mathbb{Z}/m\mathbb{Z}$ using the 
rule 
$$
[n] + [n'] := [n+n']
$$
and we multiply via 
$$
[n] \cdot [n'] := [nn']
$$

This is tagged as a lemma because rules we have written down for outputs 
depend, ostensibly, on the choice of representative for the equivalence class. 
For example, mod $5$, we have 
$$
[22] + [3] = [25]
$$
and 
$$
[2] + [3] = [5]
$$
But $[22] = [2]$ so we better have $[25] = [5]$. Indeed we do.

{% proof %}
We need to check that if $n_1 \equiv n_2 \mod m$ and $n_1' \equiv n_2' \mod m$ 
then $n_1 + n_1' \equiv n_2 + n_2' \mod m$ and $n_1n_1' \equiv n_2n_2' \mod m$. 

Assume that $n_1 \equiv n_2 \mod m$ and $n_1' \equiv n_2' \mod m$. Then by definition 
$n_1 - n_2 = c_1m$ and $n_1' - n_2' = c_2 m$. Then 
$$
n_1 + n_1' - (n_2 + n_2') = c_1 m + c_2 m + (c_1+c_2) m
$$
so indeed $n_1 + n_1' \equiv n_2 + n_2' \mod m$. 

Being a little more clever, we have 
$$
n_1 \cdot n_1' - n_2 \cdot n_2' = n_1 \cdot n_1' - n_1 \cdot n_2' + n_1 \cdot n_2' - 
n_1' \cdot n_2' = n_1c_2m - n_2'c_1 m= (n_1c_2 - n_2'c_1)m 
$$
{% endproof %}

**Example**. Let's work out the multiplication table for $\mathbb{Z}/5\mathbb{Z}$. 
We have 

| | $[0]$ | $[1]$ | $[2]$ | $[3]$ | $[4]$ | 
| :---:   | :---:   |  :---: |:---: |:---: | :---: |
| $[0]$ | $[0]$ | $[0]$ | $[0]$ | $[0]$ | $[0]$ | 
| $[1]$ | $[0]$ | $[1]$ | $[2]$ | $[3]$ | $[4]$ | 
| $[2]$ | $[0]$ | $[2]$ | $[4]$ | $[1]$ | $[3]$ | 
| $[3]$ | $[0]$ | $[3]$ | $[1]$ | $[4]$ | $[2]$ | 
| $[4]$ | $[0]$ | $[4]$ | $[3]$ | $[2]$ | $[1]$ | 
