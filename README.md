# Heine-Borel Theorem for Cuts

This repository contains formalization in Rocq (Coq) of an intuitionistic (but not constructive) proof of the following propositions:

A set $L$ of rational numbers $\mathbb{Q}$ is called a *lowercut* if
- $\forall a,b : \mathbb{Q}, a < b \land b \in L \to a \in L$.
- $\forall a : \mathbb{Q}, a \in L \to \exists b : \mathbb{Q}, a < b \land b \in L$.
 
Symmetrically, a set $U$ is called an *uppercut* if
- $\forall a,b : \mathbb{Q}, a < b \land a \in U \to b \in U$.
- $\forall b : \mathbb{Q}, b \in U \to \exists a : \mathbb{Q}, a < b \land a \in U$.
 

For a lowercut $L$ and an uppercut $U$, we write
- $\overline{L} := \Set{b : \mathbb{Q} \mid \forall a : \mathbb{Q}, a < b \to a \in L}$,
- $\overline{U} := \Set{a : \mathbb{Q} \mid \forall b : \mathbb{Q}, a < b \to b \in U}$.

Let $a, b \in \mathbb{Q}$ be a pair of rational numbers and let $(q_i, r_i)_{i\in \iota}$ be an indexed family of pairs of rational numbers. 
1. We assume that, for any lowercut $L$, if $q_i \in L \to r_i \in \overline{L}$ for all $i\in\iota$, then $a \in \overline{L}\to b \in L$. Then, there exists a finite subset of indices $i_0, \ldots, i_{n-1} \in \iota$ such that, for any lowercut $L$, if $q_i \in L \to r_i \in \overline{L}$ for all $i=i_0,\ldots, i_{n-1}$, then $a \in \overline{L}\to b \in L$.
2. The assumption in the above proposition is equivalent to the condition that, for any uppercut $U$, if $r_i \in U \to q_i \in \overline{U}$ for all $i\in\iota$, then $b \in \overline{U} \to a \in U$.

Note that the above assumption is classically equivalent to the condition that open intervals $(q_i, r_i)$ cover the closed interval $[a,b]$.
Thus, the first proposition is classically equivalent to the Heine-Borel theorem for closed intervals.
