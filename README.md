# Normalization by Evaluation for Non-cumulativity

This is an online artifact of our ICFP'25 paper of the same name. The same artifact is also available
on [Zenodo](https://zenodo.org/records/15686111). Readers of this artifact are encouraged to experiment
with our artifact. 

Normalization by evaluation (NbE) based on an untyped domain model is a convenient and powerful way to
normalize terms to their 𝛽𝜂 normal forms. It enables a concise technical setup and simplicity for mechanization. 
Nevertheless, to date, untyped NbE has only been studied for cumulative universe hierarchies, and its
correctness proof critically relies on the cumulativity of the system. Therefore we are faced with the question:
whether untyped NbE applies to a non-cumulative universe hierarchy? As such a universe hierarchy is also
widely used by proof assistants like Agda and Lean, this question is also of practical significance.

Our work answers this question positively. One important property derived from non-cumulativity is
[uniqueness](NonCumulative.Ascribed.Consequences.html#7365): every term has a unique type. In light of the
uniqueness property, we work with [a Martin-Löf type theory with explicit universe levels](NonCumulative.Ascribed.Statics.Full.html#836)
ascribed in the syntactic judgments. On the semantic side, universe
levels are also explicitly managed, which leads to more complexity than the semantics with a cumulative
universe hierarchy. We prove that the NbE algorithm is [sound](NonCumulative.Ascribed.Soundness.html) and
[complete](NonCumulative.Ascribed.Completeness.html), and confirm that NbE does work
with non-cumulativity. Moreover, to capture common practice more faithfully, we also show that the explicit
annotations of universe levels, though technically useful, are logically redundant: NbE remains applicable
without these annotations. As such, we provide a mechanized foundation with NbE for non-cumulativity.

Please read [README](README.html) for our mechanization. 

This library current works with Agda 2.7.0.1 and agda-stdlib 2.1.1. 

This work is a continuation of a larger effort of [mechanizing type theory in Agda](/mech-type-theories).

## Installing Agda

It is recommended to build Agda from source. To do so, one would need to install
`stack`. This can be done via

``` bash
curl -sSL https://get.haskellstack.org/ | sh
```

Then the following script will use `stack` to install Agda in `~/.local/bin/`.

``` bash
git clone https://github.com/agda/agda
cd agda
git checkout a6fc20c # the commit id of 2.7.0.1
cp stack-8.8.4.yaml stack.yaml # choose your favourite Haskell version
stack install # it is going to take a while
cp ~/.local/bin/agda ~/.local/bin/agda-2.7.0.1
cp ~/.local/bin/agda-mode ~/.local/bin/agda-mode-2.7.0.1
```

If Agda does not run, please check to make sure it is in your PATH.

## Foundation and Assumptions

This library is implemented in safe Agda without K as much as possible. For dependent
type theories, however, it is necessary to include the extension of
induction-recursion. Functional extensionality is sometimes used for dependent type
theories as well. These extensions are completely standard, as done in many other
works. 
