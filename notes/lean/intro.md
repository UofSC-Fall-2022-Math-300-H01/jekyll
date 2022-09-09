---
layout: page
title: Lean
nav_order: 2
has_children: true
parent: Notes
reading_estimate: true
---

## Computers, mathematics, and proof

Each day brings greater 
involvement of computers in every facet of our day to day life. Mathematics 
is no different. 

Use of computers for computation in mathematics is now very well-established. 
For example, suppose we want to figure out if $2^{15485862}$ is divisible by 
$15485863$. Computing the power and then long dividing by hand would take a 
person awhile. (But there is a secret shortcut if you know some abstract 
algebra). But a well-written computer program can do it in milli-seconds. 

Another use, relevant to us directly, is the encoding mathematical ideas and proof 
in computer programs. Proofs become data which the computer can then check for 
correctness. 

Mathematicians and computer scientists have worked on this idea for decades but 
it is only relatively recently that computer checked proofs have reached a 
threshold of usability to see widespread adoption by mathematicians. 

We will use a tool called [Lean](https://leanprover.github.io) to aid us in our 
investigations of mathematics and proof in particular. To begin with, we will 
see how to represent all of proposition logic in Lean. 

