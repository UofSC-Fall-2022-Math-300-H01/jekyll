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

This $m_1$ itself could be even or odd. Let $\epilson_1$ be its reainder 
when divided by $2$. Then 
$$
m - \epsilon_0 - 2\epsilon_1 = 4m_2
$$
So 
$$ 
m \equiv \epsilon_0 + 2 \epsilon_1 \mod 4
$$

We can continue this process with 

